import PcSastLean.CPGTraversal

/-!
CPG extraction provenance.

`CPGConstruction` proves that component edges can be merged into one CPG.  This
module adds a more source-facing certificate shape: each component edge must be
backed by an extraction origin such as an AST child relation, a CFG step, a DDG
reaching-definition edge, a CDG control-dependence edge, or a call/return link.

The theorem is intentionally still conditional: it checks consistency of the
extraction witness, not parser or data-flow correctness for a production
language.  But it rules out a common CPG trust-boundary failure mode: an accepted
finding path cannot rely on a hop unless that hop has a typed extraction origin.

Claim boundary:

* Verified here: checked finding paths over merged CPG component edges can be
  paired with per-hop extraction-origin certificates, and every certified hop's
  edge kind is forced by its origin.
* External obligations: production extractors must prove that origin facts are
  correct for the real AST, CFG, DDG, CDG, call graph, and return-flow graph.
* Not modeled here: parser correctness, dominance algorithms, reaching
  definition algorithms, alias-sensitive DDG construction, or interprocedural
  summary extraction.
-/

namespace PcSastLean

inductive CPGExtractionOrigin where
  | astChild (parent child : CPGId) (loc : SourceLoc)
  | cfgStep (src dst : CPGId) (loc : SourceLoc)
  | ddgReachingDef (src dst : CPGId) (varName : Var) (loc : SourceLoc)
  | cdgControlDep (controller dependent : CPGId) (loc : SourceLoc)
  | callLink (caller callee : CPGId) (loc : SourceLoc)
  | returnLink (callee caller : CPGId) (loc : SourceLoc)
deriving DecidableEq, Repr

def CPGExtractionOrigin.src : CPGExtractionOrigin -> CPGId
  | CPGExtractionOrigin.astChild parent _ _ => parent
  | CPGExtractionOrigin.cfgStep src _ _ => src
  | CPGExtractionOrigin.ddgReachingDef src _ _ _ => src
  | CPGExtractionOrigin.cdgControlDep controller _ _ => controller
  | CPGExtractionOrigin.callLink caller _ _ => caller
  | CPGExtractionOrigin.returnLink callee _ _ => callee

def CPGExtractionOrigin.dst : CPGExtractionOrigin -> CPGId
  | CPGExtractionOrigin.astChild _ child _ => child
  | CPGExtractionOrigin.cfgStep _ dst _ => dst
  | CPGExtractionOrigin.ddgReachingDef _ dst _ _ => dst
  | CPGExtractionOrigin.cdgControlDep _ dependent _ => dependent
  | CPGExtractionOrigin.callLink _ callee _ => callee
  | CPGExtractionOrigin.returnLink _ caller _ => caller

def CPGExtractionOrigin.componentKind :
    CPGExtractionOrigin -> CPGComponentKind
  | CPGExtractionOrigin.astChild _ _ _ => CPGComponentKind.ast
  | CPGExtractionOrigin.cfgStep _ _ _ => CPGComponentKind.cfg
  | CPGExtractionOrigin.ddgReachingDef _ _ _ _ => CPGComponentKind.data
  | CPGExtractionOrigin.cdgControlDep _ _ _ => CPGComponentKind.control
  | CPGExtractionOrigin.callLink _ _ _ => CPGComponentKind.call
  | CPGExtractionOrigin.returnLink _ _ _ => CPGComponentKind.ret

def CPGExtractionOrigin.loc : CPGExtractionOrigin -> SourceLoc
  | CPGExtractionOrigin.astChild _ _ loc => loc
  | CPGExtractionOrigin.cfgStep _ _ loc => loc
  | CPGExtractionOrigin.ddgReachingDef _ _ _ loc => loc
  | CPGExtractionOrigin.cdgControlDep _ _ loc => loc
  | CPGExtractionOrigin.callLink _ _ loc => loc
  | CPGExtractionOrigin.returnLink _ _ loc => loc

def CPGExtractionOrigin.toComponentEdge
    (origin : CPGExtractionOrigin) : CPGComponentEdge :=
  { src := origin.src
  , dst := origin.dst
  , kind := origin.componentKind
  , loc := origin.loc
  }

structure CPGExtractedEdgeCert where
  origin : CPGExtractionOrigin
  component : CPGComponentEdge
deriving Repr

def CPGExtractedEdgeCert.Sound (cert : CPGExtractedEdgeCert) : Prop :=
  cert.component = cert.origin.toComponentEdge

def checkCPGExtractedEdgeCert (cert : CPGExtractedEdgeCert) : Bool :=
  decide (cert.component = cert.origin.toComponentEdge)

theorem checkCPGExtractedEdgeCert_sound
    {cert : CPGExtractedEdgeCert}
    (h : checkCPGExtractedEdgeCert cert = true) :
    cert.Sound := by
  simpa [checkCPGExtractedEdgeCert, CPGExtractedEdgeCert.Sound] using h

theorem extracted_edge_kind_forced_by_origin
    {cert : CPGExtractedEdgeCert}
    (h : cert.Sound) :
    cert.component.kind = cert.origin.componentKind := by
  rw [h]
  rfl

def CPGExtractedEdgeCert.toHop (cert : CPGExtractedEdgeCert) : CPGHop :=
  cert.component.toHop

def ExtractedHopCertified
    (certs : List CPGExtractedEdgeCert) (hop : CPGHop) : Prop :=
  exists cert,
    cert ∈ certs /\
    cert.toHop = hop /\
    cert.Sound

def ExtractedHopsCertified
    (certs : List CPGExtractedEdgeCert) (hops : List CPGHop) : Prop :=
  forall hop, hop ∈ hops -> ExtractedHopCertified certs hop

def checkExtractedHop
    (certs : List CPGExtractedEdgeCert) (hop : CPGHop) : Bool :=
  match certs with
  | [] => false
  | cert :: rest =>
      (checkCPGExtractedEdgeCert cert && decide (cert.toHop = hop)) ||
      checkExtractedHop rest hop

theorem checkExtractedHop_sound
    {certs : List CPGExtractedEdgeCert} {hop : CPGHop}
    (h : checkExtractedHop certs hop = true) :
    ExtractedHopCertified certs hop := by
  induction certs with
  | nil =>
      simp [checkExtractedHop] at h
  | cons cert rest ih =>
      simp [checkExtractedHop] at h
      cases h with
      | inl hhead =>
          exact ⟨cert, by simp, hhead.right,
            checkCPGExtractedEdgeCert_sound hhead.left⟩
      | inr htail =>
          rcases ih htail with ⟨found, hmem, hhop, hsound⟩
          exact ⟨found, by simp [hmem], hhop, hsound⟩

def checkExtractedHops
    (certs : List CPGExtractedEdgeCert) : List CPGHop -> Bool
  | [] => true
  | hop :: rest =>
      checkExtractedHop certs hop && checkExtractedHops certs rest

theorem checkExtractedHops_sound
    {certs : List CPGExtractedEdgeCert} :
    forall {hops : List CPGHop},
      checkExtractedHops certs hops = true ->
      ExtractedHopsCertified certs hops := by
  intro hops
  induction hops with
  | nil =>
      intro _ hop hmem
      simp at hmem
  | cons hop rest ih =>
      intro hcheck candidate hmem
      simp [checkExtractedHops] at hcheck
      simp at hmem
      cases hmem with
      | inl hhead =>
          subst hhead
          exact checkExtractedHop_sound hcheck.left
      | inr htail =>
          exact ih hcheck.right candidate htail

theorem extracted_hop_has_origin_edge
    {certs : List CPGExtractedEdgeCert} {hop : CPGHop}
    (h : ExtractedHopCertified certs hop) :
    exists origin : CPGExtractionOrigin,
      hop.kind = origin.componentKind.toEdgeKind /\
      hop.edge = origin.toComponentEdge.toCPGEdge := by
  rcases h with ⟨cert, _hmem, hhop, hsound⟩
  refine ⟨cert.origin, ?_, ?_⟩
  · calc
      hop.kind = cert.component.kind.toEdgeKind := by
        rw [← hhop]
        rfl
      _ = cert.origin.componentKind.toEdgeKind := by
        rw [extracted_edge_kind_forced_by_origin hsound]
  · calc
      hop.edge = cert.component.toCPGEdge := by
        rw [← hhop]
        rfl
      _ = cert.origin.toComponentEdge.toCPGEdge := by
        rw [hsound]

theorem checked_cpg_finding_with_extraction_provenance_sound
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId} {cert : CPGFindingCert}
    {edgeCerts : List CPGExtractedEdgeCert}
    (hfind :
      checkCPGFinding
        nodes (mergeComponentEdges components) sources sinks cert = true)
    (hprov : checkExtractedHops edgeCerts cert.hops = true) :
    CPGFinding
      (mergeComponentEdges components) sources sinks cert.source cert.sink /\
    ExtractedHopsCertified edgeCerts cert.hops /\
    forall hop, hop ∈ cert.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge := by
  have hcertified := checkExtractedHops_sound hprov
  exact ⟨checked_cpg_finding_sound hfind, hcertified,
    fun hop hmem => extracted_hop_has_origin_edge (hcertified hop hmem)⟩

/-! ## Demo: AST, CFG, and DDG origins certify the CPG finding path -/

def cpgAstOrigin : CPGExtractionOrigin :=
  CPGExtractionOrigin.astChild 10 11 demoLoc

def cpgCfgOrigin : CPGExtractionOrigin :=
  CPGExtractionOrigin.cfgStep 11 12 demoLoc

def cpgDdgOrigin : CPGExtractionOrigin :=
  CPGExtractionOrigin.ddgReachingDef 12 13 0 demoLoc

def cpgExtractionCerts : List CPGExtractedEdgeCert :=
  [ { origin := cpgAstOrigin, component := cpgAstComponent }
  , { origin := cpgCfgOrigin, component := cpgCfgComponent }
  , { origin := cpgDdgOrigin, component := cpgDataComponent }
  ]

example :
    checkExtractedHops cpgExtractionCerts cpgAstCfgDataCert.hops = true := by
  native_decide

example :
    CPGFinding
      (mergeComponentEdges cpgComponentGraph)
      cpgAstCfgDataQuery.sources
      cpgAstCfgDataQuery.sinks
      10
      13 /\
    ExtractedHopsCertified cpgExtractionCerts cpgAstCfgDataCert.hops /\
    forall hop, hop ∈ cpgAstCfgDataCert.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge :=
  checked_cpg_finding_with_extraction_provenance_sound
    (nodes := cpgTraversalNodes)
    (cert := cpgAstCfgDataCert)
    (edgeCerts := cpgExtractionCerts)
    (by native_decide)
    (by native_decide)

end PcSastLean
