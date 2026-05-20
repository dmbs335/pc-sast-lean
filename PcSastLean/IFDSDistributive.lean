import PcSastLean.IFDSSummary

/-!
IFDS finite-distributive flow functions.

Reps, Horwitz, and Sagiv reduce interprocedural finite distributive subset
problems to graph reachability over an exploded supergraph.  The older IFDS
modules in this repository check paths once the exploded graph already exists.
This module adds the missing bridge: sparse fact-to-fact flow relations are
finite distributive subset transformers, and each relational flow path compiles
to an ordinary IFDS path in the exploded graph.

Claim boundary:

* Verified here: finite relational flow functions distribute over list-union
  membership, and checked-by-Proposition flow paths lower to IFDS reachability.
* External obligations: a real frontend/analysis must prove that each concrete
  program statement's transfer function is represented by the emitted relation.
* Not modeled here: the tabulation worklist algorithm, complexity bounds,
  zero-value conventions, meet-over-all-valid-path optimality, or IDE weights.
-/

namespace PcSastLean

structure IFDSFactFlow where
  src : Fact
  dst : Fact
deriving DecidableEq, Repr

def applyFactFlow : List IFDSFactFlow -> List Fact -> List Fact
  | [], _ => []
  | rel :: rest, input =>
      if rel.src ∈ input then
        rel.dst :: applyFactFlow rest input
      else
        applyFactFlow rest input

theorem applyFactFlow_sound
    {flow : List IFDSFactFlow} {input : List Fact} {out : Fact}
    (h : out ∈ applyFactFlow flow input) :
    exists rel,
      rel ∈ flow /\ rel.src ∈ input /\ rel.dst = out := by
  induction flow with
  | nil =>
      simp [applyFactFlow] at h
  | cons rel rest ih =>
      by_cases hsrc : rel.src ∈ input
      · simp [applyFactFlow, hsrc] at h
        cases h with
        | inl hout =>
            exact ⟨rel, by simp, hsrc, hout.symm⟩
        | inr hrest =>
            rcases ih hrest with ⟨rel', hmem, hin, hout⟩
            exact ⟨rel', by simp [hmem], hin, hout⟩
      · simp [applyFactFlow, hsrc] at h
        rcases ih h with ⟨rel', hmem, hin, hout⟩
        exact ⟨rel', by simp [hmem], hin, hout⟩

theorem applyFactFlow_complete
    {flow : List IFDSFactFlow} {input : List Fact} {rel : IFDSFactFlow}
    (hrel : rel ∈ flow) (hin : rel.src ∈ input) :
    rel.dst ∈ applyFactFlow flow input := by
  induction flow with
  | nil =>
      simp at hrel
  | cons head rest ih =>
      by_cases hsrc : head.src ∈ input
      · simp [applyFactFlow, hsrc] at hrel ⊢
        cases hrel with
        | inl heq =>
            subst heq
            exact Or.inl rfl
        | inr htail =>
            exact Or.inr (ih htail)
      · simp [applyFactFlow, hsrc] at hrel ⊢
        cases hrel with
        | inl heq =>
            subst heq
            exact False.elim (hsrc hin)
        | inr htail =>
            exact ih htail

theorem applyFactFlow_append_distributes
    (flow : List IFDSFactFlow) (left right : List Fact) (out : Fact) :
    out ∈ applyFactFlow flow (left ++ right) <->
      out ∈ applyFactFlow flow left ++ applyFactFlow flow right := by
  constructor
  · intro h
    rcases applyFactFlow_sound h with ⟨rel, hrel, hin, hout⟩
    rw [← hout]
    cases List.mem_append.mp hin with
    | inl hleft =>
        exact List.mem_append_left
          (applyFactFlow flow right)
          (applyFactFlow_complete hrel hleft)
    | inr hright =>
        exact List.mem_append_right
          (applyFactFlow flow left)
          (applyFactFlow_complete hrel hright)
  · intro h
    cases List.mem_append.mp h with
    | inl hleft =>
        rcases applyFactFlow_sound hleft with ⟨rel, hrel, hin, hout⟩
        rw [← hout]
        exact applyFactFlow_complete hrel (List.mem_append_left right hin)
    | inr hright =>
        rcases applyFactFlow_sound hright with ⟨rel, hrel, hin, hout⟩
        rw [← hout]
        exact applyFactFlow_complete hrel (List.mem_append_right left hin)

structure IFDSFlowEdge where
  proc : ProcId
  srcPoint : Point
  dstPoint : Point
  action : Action
  flow : List IFDSFactFlow
deriving DecidableEq, Repr

def IFDSFlowEdge.explodeOne (edge : IFDSFlowEdge) (rel : IFDSFactFlow) :
    IFDSEdge :=
  { src := { proc := edge.proc, point := edge.srcPoint, fact := rel.src }
  , dst := { proc := edge.proc, point := edge.dstPoint, fact := rel.dst }
  , action := edge.action
  }

def explodeFlowEdge (edge : IFDSFlowEdge) : List IFDSEdge :=
  edge.flow.map (edge.explodeOne)

def explodeFlowGraph : List IFDSFlowEdge -> List IFDSEdge
  | [] => []
  | edge :: rest => explodeFlowEdge edge ++ explodeFlowGraph rest

theorem fact_flow_mem_explode_edge
    {edge : IFDSFlowEdge} {rel : IFDSFactFlow}
    (hrel : rel ∈ edge.flow) :
    edge.explodeOne rel ∈ explodeFlowEdge edge := by
  unfold explodeFlowEdge
  exact List.mem_map.mpr ⟨rel, hrel, rfl⟩

theorem flow_edge_mem_explode_graph
    {program : List IFDSFlowEdge} {edge : IFDSFlowEdge} {rel : IFDSFactFlow}
    (hedge : edge ∈ program) (hrel : rel ∈ edge.flow) :
    edge.explodeOne rel ∈ explodeFlowGraph program := by
  induction program with
  | nil =>
      simp at hedge
  | cons head rest ih =>
      simp [explodeFlowGraph] at hedge ⊢
      cases hedge with
      | inl heq =>
          subst heq
          exact Or.inl (fact_flow_mem_explode_edge hrel)
      | inr htail =>
          exact Or.inr (ih htail)

structure IFDSFlowHop where
  edge : IFDSFlowEdge
  rel : IFDSFactFlow
deriving DecidableEq, Repr

def IFDSFlowHop.src (hop : IFDSFlowHop) : IFDSNode :=
  { proc := hop.edge.proc, point := hop.edge.srcPoint, fact := hop.rel.src }

def IFDSFlowHop.dst (hop : IFDSFlowHop) : IFDSNode :=
  { proc := hop.edge.proc, point := hop.edge.dstPoint, fact := hop.rel.dst }

def IFDSFlowHop.toHop (hop : IFDSFlowHop) : IFDSHop :=
  { src := hop.src, dst := hop.dst, action := hop.edge.action }

def IFDSFlowHop.toEdge (hop : IFDSFlowHop) : IFDSEdge :=
  { src := hop.src, dst := hop.dst, action := hop.edge.action }

def flowHopActions : List IFDSFlowHop -> List Action
  | [] => []
  | hop :: rest => hop.edge.action :: flowHopActions rest

def flowHopsPath
    (program : List IFDSFlowEdge) :
    List IFDSFlowHop -> IFDSNode -> IFDSNode -> Prop
  | [], seed, target => seed = target
  | hop :: rest, seed, target =>
      hop.edge ∈ program /\
      hop.rel ∈ hop.edge.flow /\
      hop.src = seed /\
      flowHopsPath program rest hop.dst target

theorem flow_hop_edge_in_exploded_graph
    {program : List IFDSFlowEdge} {hop : IFDSFlowHop}
    (hedge : hop.edge ∈ program) (hrel : hop.rel ∈ hop.edge.flow) :
    hop.toEdge ∈ explodeFlowGraph program := by
  exact flow_edge_mem_explode_graph hedge hrel

theorem flowHopsPath_to_IFDSPath
    {program : List IFDSFlowEdge} :
    forall hops seed target,
      flowHopsPath program hops seed target ->
      IFDSPath (explodeFlowGraph program) seed target (flowHopActions hops) := by
  intro hops
  induction hops with
  | nil =>
      intro seed target h
      simp [flowHopsPath] at h
      subst h
      exact IFDSPath.refl seed
  | cons hop rest ih =>
      intro seed target h
      rcases h with ⟨hedge, hrel, hsrc, hrest⟩
      subst hsrc
      simp [flowHopActions]
      exact IFDSPath.cons
        (flow_hop_edge_in_exploded_graph (hop := hop) hedge hrel)
        (ih hop.dst target hrest)

structure IFDSFlowPathCert where
  seed : IFDSNode
  target : IFDSNode
  hops : List IFDSFlowHop
deriving Repr

def IFDSFlowPathCert.Valid
    (program : List IFDSFlowEdge) (seeds : List IFDSNode)
    (cert : IFDSFlowPathCert) : Prop :=
  cert.seed ∈ seeds /\
  flowHopsPath program cert.hops cert.seed cert.target /\
  ValidActions (flowHopActions cert.hops)

theorem ifds_flow_path_cert_sound
    {program : List IFDSFlowEdge} {seeds : List IFDSNode}
    {cert : IFDSFlowPathCert}
    (h : cert.Valid program seeds) :
    IFDSReachable (explodeFlowGraph program) seeds cert.target := by
  exact ⟨cert.seed, flowHopActions cert.hops, h.left,
    flowHopsPath_to_IFDSPath cert.hops cert.seed cert.target h.right.left,
    h.right.right⟩

/-! ## Demo: a sparse distributive flow relation lowers to IFDS reachability -/

def ifdsFlowSourceToCall : IFDSFlowEdge :=
  { proc := 0
  , srcPoint := 0
  , dstPoint := 1
  , action := Action.normal
  , flow := [{ src := 1, dst := 1 }]
  }

def ifdsFlowCallToReturn : IFDSFlowEdge :=
  { proc := 0
  , srcPoint := 1
  , dstPoint := 2
  , action := Action.normal
  , flow := [{ src := 1, dst := 2 }]
  }

def ifdsFlowProgram : List IFDSFlowEdge :=
  [ifdsFlowSourceToCall, ifdsFlowCallToReturn]

def ifdsFlowSeed : IFDSNode := { proc := 0, point := 0, fact := 1 }
def ifdsFlowTarget : IFDSNode := { proc := 0, point := 2, fact := 2 }

def ifdsFlowCert : IFDSFlowPathCert :=
  { seed := ifdsFlowSeed
  , target := ifdsFlowTarget
  , hops :=
      [ { edge := ifdsFlowSourceToCall, rel := { src := 1, dst := 1 } }
      , { edge := ifdsFlowCallToReturn, rel := { src := 1, dst := 2 } }
      ]
  }

theorem ifdsFlowCertValid :
    ifdsFlowCert.Valid ifdsFlowProgram [ifdsFlowSeed] := by
  simp [IFDSFlowPathCert.Valid, ifdsFlowCert, ifdsFlowProgram, ifdsFlowSeed,
    ifdsFlowTarget, flowHopsPath, IFDSFlowHop.src, IFDSFlowHop.dst,
    flowHopActions, ValidActions, runActions, stepStack, ifdsFlowSourceToCall,
    ifdsFlowCallToReturn]

example :
    IFDSReachable (explodeFlowGraph ifdsFlowProgram) [ifdsFlowSeed]
      ifdsFlowTarget :=
  ifds_flow_path_cert_sound ifdsFlowCertValid

example :
    2 ∈ applyFactFlow [{ src := 1, dst := 2 }] ([0, 1] ++ [3]) <->
      2 ∈ applyFactFlow [{ src := 1, dst := 2 }] [0, 1] ++
        applyFactFlow [{ src := 1, dst := 2 }] [3] :=
  applyFactFlow_append_distributes [{ src := 1, dst := 2 }] [0, 1] [3] 2

end PcSastLean
