import PcSastLean.CPGExtractionProvenance
import PcSastLean.CPGSanitizerTriage

/-!
No-orphan CPG adapters.

`CPGExtractionProvenance` can check that each hop in a CPG finding path has a
typed extraction origin.  This module makes that requirement part of the
adapter boundary: a CPG finding or sanitizer-triage run can be lifted only
through a checker that accepts both the ordinary CPG evidence and per-hop
extraction-origin coverage.

Claim boundary:

* Verified here: provenance-backed CPG analyzer runs and ordered-sanitizer
  triage runs cannot depend on a finding hop that lacks a checked extraction
  origin certificate.
* External obligations: production extractors still must prove that each origin
  fact is correct for the source language and analysis algorithm.
* Not modeled here: completeness of extraction, graph-query optimization,
  alias-sensitive DDG construction, dominance, parser correctness, or source-map
  correctness.
-/

namespace PcSastLean

structure CPGNoOrphanFindingCert where
  finding : CPGFindingCert
  extraction : List CPGExtractedEdgeCert
deriving Repr

def checkCPGNoOrphanFinding
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (cert : CPGNoOrphanFindingCert) : Bool :=
  checkCPGFinding nodes (mergeComponentEdges components) sources sinks cert.finding &&
  checkExtractedHops cert.extraction cert.finding.hops

def CPGNoOrphanFindingMatch
    (components : List CPGComponentEdge) (sources sinks : List CPGId)
    (cert : CPGNoOrphanFindingCert) : Prop :=
  CPGFinding
    (mergeComponentEdges components) sources sinks
    cert.finding.source cert.finding.sink /\
  ExtractedHopsCertified cert.extraction cert.finding.hops /\
  forall hop, hop ∈ cert.finding.hops ->
    exists origin : CPGExtractionOrigin,
      hop.kind = origin.componentKind.toEdgeKind /\
      hop.edge = origin.toComponentEdge.toCPGEdge

theorem checked_cpg_no_orphan_finding_sound
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId} {cert : CPGNoOrphanFindingCert}
    (h : checkCPGNoOrphanFinding nodes components sources sinks cert = true) :
    CPGNoOrphanFindingMatch components sources sinks cert := by
  simp [checkCPGNoOrphanFinding, CPGNoOrphanFindingMatch] at h
  exact checked_cpg_finding_with_extraction_provenance_sound
    (nodes := nodes)
    (components := components)
    (cert := cert.finding)
    (edgeCerts := cert.extraction)
    h.left
    h.right

def cpgNoOrphanFindingRun
    (_nodes : List CPGNode) (_components : List CPGComponentEdge)
    (_sources _sinks : List CPGId)
    (cert : CPGNoOrphanFindingCert) : AnalyzerRun :=
  { concrete := [cert.finding.sink]
  , abstract := [cert.finding.sink]
  }

theorem cpgNoOrphanFindingRun_sound
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId} {cert : CPGNoOrphanFindingCert}
    (h : checkCPGNoOrphanFinding nodes components sources sinks cert = true) :
    (cpgNoOrphanFindingRun nodes components sources sinks cert).Sound := by
  have _hmatch := checked_cpg_no_orphan_finding_sound h
  intro id hmem
  exact hmem

theorem cpgNoOrphanFindingRun_hops_have_origins
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId} {cert : CPGNoOrphanFindingCert}
    (h : checkCPGNoOrphanFinding nodes components sources sinks cert = true) :
    forall hop, hop ∈ cert.finding.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge := by
  exact (checked_cpg_no_orphan_finding_sound h).right.right

theorem cpgNoOrphanFindingRun_reports_only_cert_sink
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId} {cert : CPGNoOrphanFindingCert}
    {sink : Node}
    (h : sink ∈ (cpgNoOrphanFindingRun nodes components sources sinks cert).abstract) :
    sink = cert.finding.sink := by
  simpa [cpgNoOrphanFindingRun] using h

structure CPGNoOrphanOrderedSanitizerCert where
  ordered : CPGOrderedSanitizedTraversalCert
  extraction : List CPGExtractedEdgeCert
deriving Repr

def checkCPGNoOrphanOrderedSanitizer
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (components : List CPGComponentEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGNoOrphanOrderedSanitizerCert) : Bool :=
  checkCPGOrderedSanitizedTraversal
    nodes nodeFacts valueFacts (mergeComponentEdges components)
    policyRules sanitizerRules query cert.ordered &&
  checkExtractedHops
    cert.extraction cert.ordered.sanitized.policyBacked.finding.hops

def CPGNoOrphanOrderedSanitizerMatch
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (components : List CPGComponentEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGNoOrphanOrderedSanitizerCert) : Prop :=
  CPGOrderedSanitizedTraversalMatch
    nodes nodeFacts valueFacts (mergeComponentEdges components)
    policyRules sanitizerRules query cert.ordered /\
  ExtractedHopsCertified
    cert.extraction cert.ordered.sanitized.policyBacked.finding.hops /\
  forall hop, hop ∈ cert.ordered.sanitized.policyBacked.finding.hops ->
    exists origin : CPGExtractionOrigin,
      hop.kind = origin.componentKind.toEdgeKind /\
      hop.edge = origin.toComponentEdge.toCPGEdge

theorem checked_cpg_no_orphan_ordered_sanitizer_sound
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {components : List CPGComponentEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGNoOrphanOrderedSanitizerCert}
    (h :
      checkCPGNoOrphanOrderedSanitizer
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert = true) :
    CPGNoOrphanOrderedSanitizerMatch
      nodes nodeFacts valueFacts components policyRules sanitizerRules query cert := by
  simp [checkCPGNoOrphanOrderedSanitizer,
    CPGNoOrphanOrderedSanitizerMatch] at h
  have hprov := checkExtractedHops_sound h.right
  exact ⟨checked_cpg_ordered_sanitized_traversal_sound h.left, hprov,
    fun hop hmem => extracted_hop_has_origin_edge (hprov hop hmem)⟩

def cpgNoOrphanOrderedSanitizerRun
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (components : List CPGComponentEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGNoOrphanOrderedSanitizerCert) : AnalyzerRun :=
  orderedSanitizerRun
    nodes nodeFacts valueFacts (mergeComponentEdges components)
    policyRules sanitizerRules query cert.ordered

theorem cpgNoOrphanOrderedSanitizerRun_sound
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {components : List CPGComponentEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGNoOrphanOrderedSanitizerCert}
    (h :
      checkCPGNoOrphanOrderedSanitizer
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert = true) :
    (cpgNoOrphanOrderedSanitizerRun
      nodes nodeFacts valueFacts components policyRules sanitizerRules query cert).Sound := by
  simp [checkCPGNoOrphanOrderedSanitizer] at h
  exact orderedSanitizerRun_sound h.left

theorem cpgNoOrphanOrderedSanitizerRun_hops_have_origins
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {components : List CPGComponentEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGNoOrphanOrderedSanitizerCert}
    (h :
      checkCPGNoOrphanOrderedSanitizer
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert = true) :
    forall hop, hop ∈ cert.ordered.sanitized.policyBacked.finding.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge := by
  exact (checked_cpg_no_orphan_ordered_sanitizer_sound h).right.right

def noOrphanOrderedSanitizerTriageEvidence
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (components : List CPGComponentEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGNoOrphanOrderedSanitizerCert)
    (h :
      checkCPGNoOrphanOrderedSanitizer
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert = true) :
    TriageEvidence :=
  orderedSanitizerTriageEvidence
    nodes nodeFacts valueFacts (mergeComponentEdges components)
    policyRules sanitizerRules query cert.ordered
    (by
      simp [checkCPGNoOrphanOrderedSanitizer] at h
      exact h.left)

theorem noOrphanOrderedSanitizerTriageEvidence_sound
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (components : List CPGComponentEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGNoOrphanOrderedSanitizerCert)
    (h :
      checkCPGNoOrphanOrderedSanitizer
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert = true) :
    EvidenceSound
      (cpgNoOrphanOrderedSanitizerRun
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert).concrete
      (noOrphanOrderedSanitizerTriageEvidence
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert h) := by
  simp [cpgNoOrphanOrderedSanitizerRun,
    noOrphanOrderedSanitizerTriageEvidence,
    checkCPGNoOrphanOrderedSanitizer] at h ⊢
  exact orderedSanitizerTriageEvidence_sound
    nodes nodeFacts valueFacts (mergeComponentEdges components)
    policyRules sanitizerRules query cert.ordered h.left

/-! ## Demo: CPG runs and triage evidence require extraction origins -/

def cpgNoOrphanFindingCert : CPGNoOrphanFindingCert :=
  { finding := cpgAstCfgDataCert
  , extraction := cpgExtractionCerts
  }

example :
    checkCPGNoOrphanFinding
      cpgTraversalNodes cpgComponentGraph
      cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
      cpgNoOrphanFindingCert = true := by
  native_decide

theorem cpgNoOrphanFindingRunSound :
    (cpgNoOrphanFindingRun
      cpgTraversalNodes cpgComponentGraph
      cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
      cpgNoOrphanFindingCert).Sound :=
  cpgNoOrphanFindingRun_sound
    (nodes := cpgTraversalNodes)
    (components := cpgComponentGraph)
    (sources := cpgAstCfgDataQuery.sources)
    (sinks := cpgAstCfgDataQuery.sinks)
    (cert := cpgNoOrphanFindingCert)
    (by native_decide)

example :
    forall hop, hop ∈ cpgNoOrphanFindingCert.finding.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge :=
  cpgNoOrphanFindingRun_hops_have_origins
    (nodes := cpgTraversalNodes)
    (components := cpgComponentGraph)
    (sources := cpgAstCfgDataQuery.sources)
    (sinks := cpgAstCfgDataQuery.sinks)
    (cert := cpgNoOrphanFindingCert)
    (by native_decide)

def cpgNoOrphanOrderedSanitizerCert :
    CPGNoOrphanOrderedSanitizerCert :=
  { ordered := cpgOrderedSanitizedTraversalCert
  , extraction := cpgExtractionCerts
  }

example :
    checkCPGNoOrphanOrderedSanitizer
      cpgTraversalNodes
      cpgSanitizerFacts
      cpgValueFlowFacts
      cpgComponentGraph
      cpgPolicyRules
      cpgSanitizerRules
      cpgNodePredicateQuery
      cpgNoOrphanOrderedSanitizerCert = true := by
  native_decide

theorem cpgNoOrphanOrderedSanitizerRunSound :
    (cpgNoOrphanOrderedSanitizerRun
      cpgTraversalNodes
      cpgSanitizerFacts
      cpgValueFlowFacts
      cpgComponentGraph
      cpgPolicyRules
      cpgSanitizerRules
      cpgNodePredicateQuery
      cpgNoOrphanOrderedSanitizerCert).Sound :=
  cpgNoOrphanOrderedSanitizerRun_sound
    (nodes := cpgTraversalNodes)
    (nodeFacts := cpgSanitizerFacts)
    (valueFacts := cpgValueFlowFacts)
    (components := cpgComponentGraph)
    (policyRules := cpgPolicyRules)
    (sanitizerRules := cpgSanitizerRules)
    (query := cpgNodePredicateQuery)
    (cert := cpgNoOrphanOrderedSanitizerCert)
    (by native_decide)

example :
    forall hop,
      hop ∈
        cpgNoOrphanOrderedSanitizerCert.ordered.sanitized.policyBacked.finding.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge :=
  cpgNoOrphanOrderedSanitizerRun_hops_have_origins
    (nodes := cpgTraversalNodes)
    (nodeFacts := cpgSanitizerFacts)
    (valueFacts := cpgValueFlowFacts)
    (components := cpgComponentGraph)
    (policyRules := cpgPolicyRules)
    (sanitizerRules := cpgSanitizerRules)
    (query := cpgNodePredicateQuery)
    (cert := cpgNoOrphanOrderedSanitizerCert)
    (by native_decide)

end PcSastLean
