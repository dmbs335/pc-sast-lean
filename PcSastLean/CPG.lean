import PcSastLean.IFDSFixpoint

/-!
Code Property Graph certificates.

CPG/CodeQL/Joern-style SAST represents code as a typed graph that combines
syntax, control flow, and dependence edges.  Queries are graph traversals over
that graph.  This module verifies the artifact that a CPG engine can emit for a
finding: a typed path from a source node to a sink node whose hops are real CPG
edges with source-location provenance.

The module is intentionally small: it verifies query-path evidence, not the full
query optimizer.
-/

namespace PcSastLean

abbrev CPGId := Nat
abbrev FileId := Nat
abbrev Line := Nat
abbrev Col := Nat

inductive CPGNodeKind where
  | expr
  | stmt
  | call
  | param
  | ret
  | literal
deriving DecidableEq, Repr

inductive CPGEdgeKind where
  | ast
  | cfg
  | data
  | control
  | call
  | ret
deriving DecidableEq, Repr

structure SourceLoc where
  file : FileId
  line : Line
  col : Col
deriving DecidableEq, Repr

structure CPGNode where
  id : CPGId
  kind : CPGNodeKind
  loc : SourceLoc
deriving DecidableEq, Repr

structure CPGEdge where
  src : CPGId
  dst : CPGId
  kind : CPGEdgeKind
  loc : SourceLoc
deriving DecidableEq, Repr

def nodeIds (nodes : List CPGNode) : List CPGId :=
  nodes.map (fun n => n.id)

def HasNode (nodes : List CPGNode) (id : CPGId) : Prop :=
  exists n, n ∈ nodes /\ n.id = id

def WellFormedCPG (nodes : List CPGNode) (edges : List CPGEdge) : Prop :=
  forall e, e ∈ edges -> HasNode nodes e.src /\ HasNode nodes e.dst

def checkHasNode (nodes : List CPGNode) (id : CPGId) : Bool :=
  decide (id ∈ nodeIds nodes)

def checkWellFormedEdges (nodes : List CPGNode) : List CPGEdge -> Bool
  | [] => true
  | e :: rest =>
      checkHasNode nodes e.src &&
      checkHasNode nodes e.dst &&
      checkWellFormedEdges nodes rest

theorem checkHasNode_sound
    {nodes : List CPGNode} {id : CPGId}
    (h : checkHasNode nodes id = true) :
    HasNode nodes id := by
  unfold checkHasNode nodeIds at h
  have hmem : id ∈ nodes.map (fun n => n.id) := of_decide_eq_true h
  rcases List.mem_map.mp hmem with ⟨n, hn, hid⟩
  exact ⟨n, hn, hid⟩

inductive CPGPath (edges : List CPGEdge) : CPGId -> CPGId -> List CPGEdgeKind -> Prop
  | refl (n : CPGId) : CPGPath edges n n []
  | cons {a b c : CPGId} {k : CPGEdgeKind} {ks : List CPGEdgeKind} {loc : SourceLoc} :
      { src := a, dst := b, kind := k, loc := loc } ∈ edges ->
      CPGPath edges b c ks ->
      CPGPath edges a c (k :: ks)

def CPGReachableByKinds
    (edges : List CPGEdge) (src dst : CPGId) (kinds : List CPGEdgeKind) : Prop :=
  CPGPath edges src dst kinds

structure CPGHop where
  src : CPGId
  dst : CPGId
  kind : CPGEdgeKind
  loc : SourceLoc
deriving DecidableEq, Repr

def CPGHop.edge (h : CPGHop) : CPGEdge :=
  { src := h.src, dst := h.dst, kind := h.kind, loc := h.loc }

def cpgHopKinds (hops : List CPGHop) : List CPGEdgeKind :=
  hops.map (fun h => h.kind)

def cpgHopLocs (hops : List CPGHop) : List SourceLoc :=
  hops.map (fun h => h.loc)

def cpgHopsPath (edges : List CPGEdge) : List CPGHop -> CPGId -> CPGId -> Prop
  | [], src, dst => src = dst
  | hop :: rest, src, dst =>
      hop.src = src /\
      hop.edge ∈ edges /\
      cpgHopsPath edges rest hop.dst dst

def checkCPGHops (edges : List CPGEdge) : List CPGHop -> CPGId -> CPGId -> Bool
  | [], src, dst => decide (src = dst)
  | hop :: rest, src, dst =>
      decide (hop.src = src) &&
      decide (hop.edge ∈ edges) &&
      checkCPGHops edges rest hop.dst dst

theorem checkCPGHops_sound
    {edges : List CPGEdge} :
    forall hops src dst,
      checkCPGHops edges hops src dst = true ->
      cpgHopsPath edges hops src dst := by
  intro hops
  induction hops with
  | nil =>
      intro src dst h
      simp [checkCPGHops, cpgHopsPath] at h
      exact h
  | cons hop rest ih =>
      intro src dst h
      simp [checkCPGHops, cpgHopsPath] at h
      exact And.intro h.left.left (And.intro h.left.right (ih hop.dst dst h.right))

theorem cpgHopsPath_to_CPGPath
    {edges : List CPGEdge} :
    forall hops src dst,
      cpgHopsPath edges hops src dst ->
      CPGPath edges src dst (cpgHopKinds hops) := by
  intro hops
  induction hops with
  | nil =>
      intro src dst h
      simp [cpgHopsPath] at h
      subst h
      exact CPGPath.refl src
  | cons hop rest ih =>
      intro src dst h
      rcases h with ⟨hsrc, hedge, hrest⟩
      subst hsrc
      simp [cpgHopKinds]
      exact CPGPath.cons hedge (ih hop.dst dst hrest)

structure CPGFindingCert where
  source : CPGId
  sink : CPGId
  hops : List CPGHop
deriving Repr

def checkCPGFinding
    (nodes : List CPGNode) (edges : List CPGEdge)
    (sources sinks : List CPGId) (cert : CPGFindingCert) : Bool :=
  checkHasNode nodes cert.source &&
  checkHasNode nodes cert.sink &&
  decide (cert.source ∈ sources) &&
  decide (cert.sink ∈ sinks) &&
  checkCPGHops edges cert.hops cert.source cert.sink

def CPGFinding
    (edges : List CPGEdge) (sources sinks : List CPGId)
    (source sink : CPGId) : Prop :=
  source ∈ sources /\
  sink ∈ sinks /\
  exists kinds, CPGPath edges source sink kinds

theorem checked_cpg_finding_sound
    {nodes : List CPGNode} {edges : List CPGEdge}
    {sources sinks : List CPGId} {cert : CPGFindingCert}
    (h : checkCPGFinding nodes edges sources sinks cert = true) :
    CPGFinding edges sources sinks cert.source cert.sink := by
  simp [checkCPGFinding, CPGFinding] at h
  have hpath := cpgHopsPath_to_CPGPath cert.hops cert.source cert.sink
    (checkCPGHops_sound cert.hops cert.source cert.sink h.right)
  exact And.intro h.left.left.right (And.intro h.left.right
    (Exists.intro (cpgHopKinds cert.hops) hpath))

/-! ## Demo -/

def demoLoc : SourceLoc := { file := 0, line := 1, col := 1 }

def cpgSourceNode : CPGNode :=
  { id := 1, kind := CPGNodeKind.call, loc := demoLoc }

def cpgExprNode : CPGNode :=
  { id := 2, kind := CPGNodeKind.expr, loc := { file := 0, line := 2, col := 5 } }

def cpgSinkNode : CPGNode :=
  { id := 3, kind := CPGNodeKind.call, loc := { file := 0, line := 3, col := 1 } }

def cpgNodes : List CPGNode := [cpgSourceNode, cpgExprNode, cpgSinkNode]

def cpgEdges : List CPGEdge :=
  [ { src := 1, dst := 2, kind := CPGEdgeKind.data, loc := demoLoc }
  , { src := 2, dst := 3, kind := CPGEdgeKind.data, loc := demoLoc }
  ]

def cpgCert : CPGFindingCert :=
  { source := 1
  , sink := 3
  , hops :=
      [ { src := 1, dst := 2, kind := CPGEdgeKind.data, loc := demoLoc }
      , { src := 2, dst := 3, kind := CPGEdgeKind.data, loc := demoLoc }
      ]
  }

example : checkCPGFinding cpgNodes cpgEdges [1] [3] cpgCert = true := by
  native_decide

example : CPGFinding cpgEdges [1] [3] 1 3 :=
  checked_cpg_finding_sound (nodes := cpgNodes) (cert := cpgCert) (by native_decide)

end PcSastLean
