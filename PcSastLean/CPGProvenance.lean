import PcSastLean.CPG

/-!
CPG edge provenance.

`CPG.lean` checks that a query path exists in a CPG.  The next trust-boundary
question is: why should the CPG edges themselves be trusted?

This module adds a small provenance layer for data-dependence edges extracted
from the toy source language in `ExtractionGate`.  A CPG data edge is accepted
only when it is justified by a source statement such as assignment/sanitization
or by a source/sink boundary fact.

Claim boundary:

* Verified here: path-specific CPG hop provenance can be checked, and typed edge
  reasons must match edge kinds.
* External obligations: production CPG builders must provide extraction
  provenance for AST, CFG, DDG, CDG, call, and return edges.
* Not modeled here: complete real-language CPG construction rules or parser
  correctness.
-/

namespace PcSastLean

inductive DataEdgeReason where
  | sourceValue (stmt : SourceStmt)
  | sanitizerFlow (stmt : SourceStmt)
  | sinkUse (stmt : SourceStmt)
deriving Repr

structure CPGEdgeCert where
  edge : CPGEdge
  reason : DataEdgeReason
deriving Repr

inductive CPGEdgeReason where
  | dataFlow (reason : DataEdgeReason)
  | astChild
  | cfgStep
  | controlDep
  | callEdge
  | returnEdge
deriving Repr

structure TypedCPGEdgeCert where
  edge : CPGEdge
  reason : CPGEdgeReason
deriving Repr

def stmtHasDataFlow (src dst : Var) : SourceStmt -> Prop
  | SourceStmt.input v => src = v /\ dst = v
  | SourceStmt.escape out inn _ => src = inn /\ dst = out
  | SourceStmt.output inn _ _ => src = inn /\ dst = inn

def DataEdgeSoundForStmt (edge : CPGEdge) (stmt : SourceStmt) : Prop :=
  edge.kind = CPGEdgeKind.data /\
  stmtHasDataFlow edge.src edge.dst stmt

def CPGEdgeCert.Sound (cert : CPGEdgeCert) : Prop :=
  match cert.reason with
  | DataEdgeReason.sourceValue stmt => DataEdgeSoundForStmt cert.edge stmt
  | DataEdgeReason.sanitizerFlow stmt => DataEdgeSoundForStmt cert.edge stmt
  | DataEdgeReason.sinkUse stmt => DataEdgeSoundForStmt cert.edge stmt

def TypedCPGEdgeCert.Sound (cert : TypedCPGEdgeCert) : Prop :=
  match cert.reason with
  | CPGEdgeReason.dataFlow reason =>
      CPGEdgeCert.Sound { edge := cert.edge, reason := reason }
  | CPGEdgeReason.astChild => cert.edge.kind = CPGEdgeKind.ast
  | CPGEdgeReason.cfgStep => cert.edge.kind = CPGEdgeKind.cfg
  | CPGEdgeReason.controlDep => cert.edge.kind = CPGEdgeKind.control
  | CPGEdgeReason.callEdge => cert.edge.kind = CPGEdgeKind.call
  | CPGEdgeReason.returnEdge => cert.edge.kind = CPGEdgeKind.ret

theorem edge_cert_implies_data_edge
    {cert : CPGEdgeCert}
    (h : cert.Sound) :
    cert.edge.kind = CPGEdgeKind.data := by
  unfold CPGEdgeCert.Sound at h
  split at h <;> exact h.left

theorem typed_edge_cert_kind_sound
    {cert : TypedCPGEdgeCert}
    (h : cert.Sound) :
    match cert.reason with
    | CPGEdgeReason.dataFlow _ => cert.edge.kind = CPGEdgeKind.data
    | CPGEdgeReason.astChild => cert.edge.kind = CPGEdgeKind.ast
    | CPGEdgeReason.cfgStep => cert.edge.kind = CPGEdgeKind.cfg
    | CPGEdgeReason.controlDep => cert.edge.kind = CPGEdgeKind.control
    | CPGEdgeReason.callEdge => cert.edge.kind = CPGEdgeKind.call
    | CPGEdgeReason.returnEdge => cert.edge.kind = CPGEdgeKind.ret := by
  unfold TypedCPGEdgeCert.Sound at h
  split at h
  · exact edge_cert_implies_data_edge h
  · exact h
  · exact h
  · exact h
  · exact h
  · exact h

def CPGEdgesCertified (certs : List CPGEdgeCert) (edges : List CPGEdge) : Prop :=
  forall e, e ∈ edges -> exists cert, cert ∈ certs /\ cert.edge = e /\ cert.Sound

theorem certified_edge_sound
    {certs : List CPGEdgeCert} {edges : List CPGEdge} {e : CPGEdge}
    (hall : CPGEdgesCertified certs edges)
    (he : e ∈ edges) :
    exists cert, cert ∈ certs /\ cert.edge = e /\ cert.Sound :=
  hall e he

def CPGHopCertified (certs : List TypedCPGEdgeCert) (hop : CPGHop) : Prop :=
  exists cert, cert ∈ certs /\ cert.edge = hop.edge /\ cert.Sound

def CPGHopsCertified (certs : List TypedCPGEdgeCert) (hops : List CPGHop) : Prop :=
  forall hop, hop ∈ hops -> CPGHopCertified certs hop

theorem checked_cpg_finding_path_provenance_sound
    {nodes : List CPGNode} {edges : List CPGEdge}
    {sources sinks : List CPGId} {cert : CPGFindingCert}
    {edgeCerts : List TypedCPGEdgeCert}
    (hfind : checkCPGFinding nodes edges sources sinks cert = true)
    (hhops : CPGHopsCertified edgeCerts cert.hops) :
    CPGFinding edges sources sinks cert.source cert.sink /\
    forall hop, hop ∈ cert.hops -> CPGHopCertified edgeCerts hop := by
  exact And.intro (checked_cpg_finding_sound hfind) hhops

theorem cpg_path_edges_have_provenance
    {certs : List CPGEdgeCert} {edges : List CPGEdge}
    (hall : CPGEdgesCertified certs edges) :
    forall {src dst kinds},
      CPGPath edges src dst kinds ->
      forall e, e ∈ edges -> exists cert, cert ∈ certs /\ cert.edge = e /\ cert.Sound := by
  intro src dst kinds _path e he
  exact hall e he

theorem checked_cpg_finding_with_provenance_sound
    {nodes : List CPGNode} {edges : List CPGEdge}
    {sources sinks : List CPGId} {cert : CPGFindingCert}
    {edgeCerts : List CPGEdgeCert}
    (hfind : checkCPGFinding nodes edges sources sinks cert = true)
    (hedges : CPGEdgesCertified edgeCerts edges) :
    CPGFinding edges sources sinks cert.source cert.sink /\
    forall e, e ∈ edges -> exists ec, ec ∈ edgeCerts /\ ec.edge = e /\ ec.Sound := by
  exact And.intro (checked_cpg_finding_sound hfind) hedges

/-! ## Demo -/

def sourceStmtForCPG1 : SourceStmt :=
  SourceStmt.escape 2 1 SinkKind.html

def sourceStmtForCPG2 : SourceStmt :=
  SourceStmt.output 2 SinkKind.html 61

def cpgProvEdge1 : CPGEdge :=
  { src := 1, dst := 2, kind := CPGEdgeKind.data, loc := demoLoc }

def cpgProvEdge2 : CPGEdge :=
  { src := 2, dst := 2, kind := CPGEdgeKind.data, loc := demoLoc }

def cpgProvEdges : List CPGEdge := [cpgProvEdge1, cpgProvEdge2]

def cpgProvCerts : List CPGEdgeCert :=
  [ { edge := cpgProvEdge1, reason := DataEdgeReason.sanitizerFlow sourceStmtForCPG1 }
  , { edge := cpgProvEdge2, reason := DataEdgeReason.sinkUse sourceStmtForCPG2 }
  ]

def typedCpgProvCerts : List TypedCPGEdgeCert :=
  [ { edge := cpgProvEdge1
    , reason := CPGEdgeReason.dataFlow (DataEdgeReason.sanitizerFlow sourceStmtForCPG1)
    }
  ]

theorem cpgProvEdgesCertified :
    CPGEdgesCertified cpgProvCerts cpgProvEdges := by
  intro e he
  have hcases : e = cpgProvEdge1 ∨ e = cpgProvEdge2 := by
    simpa [cpgProvEdges] using he
  cases hcases with
  | inl h1 =>
      subst h1
      refine ⟨{ edge := cpgProvEdge1, reason := DataEdgeReason.sanitizerFlow sourceStmtForCPG1 }, ?_, rfl, ?_⟩
      · simp [cpgProvCerts]
      · simp [CPGEdgeCert.Sound, DataEdgeSoundForStmt, stmtHasDataFlow,
          cpgProvEdge1, sourceStmtForCPG1]
  | inr h2 =>
      subst h2
      refine ⟨{ edge := cpgProvEdge2, reason := DataEdgeReason.sinkUse sourceStmtForCPG2 }, ?_, rfl, ?_⟩
      · simp [cpgProvCerts]
      · simp [CPGEdgeCert.Sound, DataEdgeSoundForStmt, stmtHasDataFlow,
          cpgProvEdge2, sourceStmtForCPG2]

def cpgProvFindingCert : CPGFindingCert :=
  { source := 1
  , sink := 2
  , hops :=
      [ { src := 1, dst := 2, kind := CPGEdgeKind.data, loc := demoLoc } ]
  }

example :
    checkCPGFinding cpgNodes cpgProvEdges [1] [2] cpgProvFindingCert = true := by
  native_decide

theorem typedCpgProvHopsCertified :
    CPGHopsCertified typedCpgProvCerts cpgProvFindingCert.hops := by
  intro hop hhop
  have hhopEq :
      hop = { src := 1, dst := 2, kind := CPGEdgeKind.data, loc := demoLoc } := by
    simpa [cpgProvFindingCert] using hhop
  subst hhopEq
  refine ⟨
    { edge := cpgProvEdge1
    , reason := CPGEdgeReason.dataFlow (DataEdgeReason.sanitizerFlow sourceStmtForCPG1)
    }, ?_, ?_, ?_⟩
  · simp [typedCpgProvCerts]
  · simp [CPGHop.edge, cpgProvEdge1]
  · simp [TypedCPGEdgeCert.Sound, CPGEdgeCert.Sound, DataEdgeSoundForStmt,
      stmtHasDataFlow, cpgProvEdge1, sourceStmtForCPG1]

example :
    CPGFinding cpgProvEdges [1] [2] 1 2 /\
    forall hop, hop ∈ cpgProvFindingCert.hops ->
      CPGHopCertified typedCpgProvCerts hop :=
  checked_cpg_finding_path_provenance_sound
    (nodes := cpgNodes)
    (cert := cpgProvFindingCert)
    (edgeCerts := typedCpgProvCerts)
    (by native_decide)
    typedCpgProvHopsCertified

example :
    CPGFinding cpgProvEdges [1] [2] 1 2 /\
    forall e, e ∈ cpgProvEdges ->
      exists ec, ec ∈ cpgProvCerts /\ ec.edge = e /\ ec.Sound :=
  checked_cpg_finding_with_provenance_sound
    (nodes := cpgNodes)
    (cert := cpgProvFindingCert)
    (edgeCerts := cpgProvCerts)
    (by native_decide)
    cpgProvEdgesCertified

end PcSastLean
