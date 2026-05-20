import PcSastLean.ExtractionGate

/-!
IFDS-style valid-path certificates.

IFDS/IDE analyses explain a large family of practical SAST taint engines.  The
key shape is an exploded supergraph: nodes are program points paired with dataflow
facts, and interprocedural paths must respect call/return matching.

This module does not implement a full IFDS solver yet.  Instead, it formalizes a
proof-carrying certificate for one IFDS finding:

* every hop is an edge in the exploded supergraph;
* call/return actions are balanced;
* the first fact is a seed;
* therefore the final fact is reachable by a valid interprocedural path.
-/

namespace PcSastLean

abbrev ProcId := Nat
abbrev Point := Nat
abbrev Fact := Nat
abbrev Frame := Nat

structure IFDSNode where
  proc : ProcId
  point : Point
  fact : Fact
deriving DecidableEq, Repr

inductive Action where
  | normal : Action
  | call (frame : Frame) : Action
  | ret (frame : Frame) : Action
deriving DecidableEq, Repr

structure IFDSEdge where
  src : IFDSNode
  dst : IFDSNode
  action : Action
deriving DecidableEq, Repr

def stepStack (stack : List Frame) : Action -> Option (List Frame)
  | Action.normal => some stack
  | Action.call f => some (f :: stack)
  | Action.ret f =>
      match stack with
      | [] => none
      | top :: rest => if top = f then some rest else none

def runActions : List Frame -> List Action -> Option (List Frame)
  | stack, [] => some stack
  | stack, a :: rest =>
      match stepStack stack a with
      | none => none
      | some stack' => runActions stack' rest

def ValidActions (actions : List Action) : Prop :=
  runActions [] actions = some []

def checkValidActions (actions : List Action) : Bool :=
  match runActions [] actions with
  | some [] => true
  | _ => false

theorem checkValidActions_sound
    {actions : List Action}
    (h : checkValidActions actions = true) :
    ValidActions actions := by
  unfold checkValidActions ValidActions at *
  cases hrun : runActions [] actions with
  | none =>
      simp [hrun] at h
  | some stack =>
      cases stack with
      | nil =>
          rfl
      | cons top rest =>
          simp [hrun] at h

inductive IFDSPath (graph : List IFDSEdge) : IFDSNode -> IFDSNode -> List Action -> Prop
  | refl (n : IFDSNode) : IFDSPath graph n n []
  | cons {a b c : IFDSNode} {act : Action} {acts : List Action} :
      { src := a, dst := b, action := act } ∈ graph ->
      IFDSPath graph b c acts ->
      IFDSPath graph a c (act :: acts)

def IFDSReachable
    (graph : List IFDSEdge) (seeds : List IFDSNode) (target : IFDSNode) : Prop :=
  exists seed actions,
    seed ∈ seeds /\
    IFDSPath graph seed target actions /\
    ValidActions actions

structure IFDSFindingCert where
  seed : IFDSNode
  target : IFDSNode
  actions : List Action
deriving Repr

def IFDSFindingCert.Valid
    (graph : List IFDSEdge) (seeds : List IFDSNode) (cert : IFDSFindingCert) : Prop :=
  cert.seed ∈ seeds /\
  IFDSPath graph cert.seed cert.target cert.actions /\
  ValidActions cert.actions

theorem ifds_finding_cert_sound
    {graph : List IFDSEdge} {seeds : List IFDSNode} {cert : IFDSFindingCert}
    (h : cert.Valid graph seeds) :
    IFDSReachable graph seeds cert.target := by
  exact Exists.intro cert.seed (Exists.intro cert.actions h)

/-! ## Decidable checker for edge-by-edge certificates -/

structure IFDSHop where
  src : IFDSNode
  dst : IFDSNode
  action : Action
deriving DecidableEq, Repr

def hopEdge (h : IFDSHop) : IFDSEdge :=
  { src := h.src, dst := h.dst, action := h.action }

def hopActions (hops : List IFDSHop) : List Action :=
  hops.map (fun h => h.action)

def hopsPath (graph : List IFDSEdge) : List IFDSHop -> IFDSNode -> IFDSNode -> Prop
  | [], seed, target => seed = target
  | hop :: rest, seed, target =>
      hop.src = seed /\
      hopEdge hop ∈ graph /\
      hopsPath graph rest hop.dst target

def checkHops (graph : List IFDSEdge) : List IFDSHop -> IFDSNode -> IFDSNode -> Bool
  | [], seed, target => decide (seed = target)
  | hop :: rest, seed, target =>
      decide (hop.src = seed) &&
      decide (hopEdge hop ∈ graph) &&
      checkHops graph rest hop.dst target

theorem checkHops_sound
    {graph : List IFDSEdge} :
    forall hops seed target,
      checkHops graph hops seed target = true ->
      hopsPath graph hops seed target := by
  intro hops
  induction hops with
  | nil =>
      intro seed target h
      simp [checkHops, hopsPath] at h
      exact h
  | cons hop rest ih =>
      intro seed target h
      simp [checkHops, hopsPath] at h
      exact And.intro h.left.left (And.intro h.left.right (ih hop.dst target h.right))

theorem hopsPath_to_IFDSPath
    {graph : List IFDSEdge} :
    forall hops seed target,
      hopsPath graph hops seed target ->
      IFDSPath graph seed target (hopActions hops) := by
  intro hops
  induction hops with
  | nil =>
      intro seed target h
      simp [hopsPath] at h
      subst h
      exact IFDSPath.refl seed
  | cons hop rest ih =>
      intro seed target h
      rcases h with ⟨hsrc, hedge, hrest⟩
      subst hsrc
      simp [hopActions]
      exact IFDSPath.cons hedge (ih hop.dst target hrest)

structure IFDSCheckedCert where
  seed : IFDSNode
  target : IFDSNode
  hops : List IFDSHop
deriving Repr

def checkIFDSCert
    (graph : List IFDSEdge) (seeds : List IFDSNode) (cert : IFDSCheckedCert) : Bool :=
  decide (cert.seed ∈ seeds) &&
  checkHops graph cert.hops cert.seed cert.target &&
  checkValidActions (hopActions cert.hops)

theorem checked_ifds_cert_sound
    {graph : List IFDSEdge} {seeds : List IFDSNode} {cert : IFDSCheckedCert}
    (h : checkIFDSCert graph seeds cert = true) :
    IFDSReachable graph seeds cert.target := by
  simp [checkIFDSCert] at h
  have hpath := hopsPath_to_IFDSPath cert.hops cert.seed cert.target
    (checkHops_sound cert.hops cert.seed cert.target h.left.right)
  exact Exists.intro cert.seed
    (Exists.intro (hopActions cert.hops)
      (And.intro h.left.left (And.intro hpath (checkValidActions_sound h.right))))

/-! ## Demo: balanced valid path vs unmatched return -/

def ifdsSeed : IFDSNode := { proc := 0, point := 0, fact := 1 }
def ifdsCallNode : IFDSNode := { proc := 0, point := 1, fact := 1 }
def ifdsCalleeNode : IFDSNode := { proc := 1, point := 0, fact := 1 }
def ifdsReturnNode : IFDSNode := { proc := 0, point := 2, fact := 1 }
def ifdsSinkNode : IFDSNode := { proc := 0, point := 3, fact := 1 }

def ifdsGraph : List IFDSEdge :=
  [ { src := ifdsSeed, dst := ifdsCallNode, action := Action.normal }
  , { src := ifdsCallNode, dst := ifdsCalleeNode, action := Action.call 7 }
  , { src := ifdsCalleeNode, dst := ifdsReturnNode, action := Action.ret 7 }
  , { src := ifdsReturnNode, dst := ifdsSinkNode, action := Action.normal }
  ]

def ifdsCert : IFDSCheckedCert :=
  { seed := ifdsSeed
  , target := ifdsSinkNode
  , hops :=
      [ { src := ifdsSeed, dst := ifdsCallNode, action := Action.normal }
      , { src := ifdsCallNode, dst := ifdsCalleeNode, action := Action.call 7 }
      , { src := ifdsCalleeNode, dst := ifdsReturnNode, action := Action.ret 7 }
      , { src := ifdsReturnNode, dst := ifdsSinkNode, action := Action.normal }
      ]
  }

example : checkIFDSCert ifdsGraph [ifdsSeed] ifdsCert = true := by
  native_decide

example : IFDSReachable ifdsGraph [ifdsSeed] ifdsSinkNode :=
  checked_ifds_cert_sound (cert := ifdsCert) (by native_decide)

def badIFDSCert : IFDSCheckedCert :=
  { ifdsCert with
    hops :=
      [ { src := ifdsSeed, dst := ifdsCallNode, action := Action.normal }
      , { src := ifdsCallNode, dst := ifdsCalleeNode, action := Action.call 7 }
      , { src := ifdsCalleeNode, dst := ifdsReturnNode, action := Action.ret 8 }
      , { src := ifdsReturnNode, dst := ifdsSinkNode, action := Action.normal }
      ]
  }

example : checkIFDSCert ifdsGraph [ifdsSeed] badIFDSCert = false := by
  native_decide

end PcSastLean
