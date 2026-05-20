import PcSastLean.SourceBackedAdapters
import PcSastLean.CPGNoOrphanAdapter

/-!
Source-backed no-orphan CPG adapters.

`SourceBackedAdapters` maps artifact-level findings to source-level CI findings
with source/artifact sink provenance.  `CPGNoOrphanAdapter` ensures that CPG
artifact runs cannot depend on a finding path with an orphan hop.  This module
combines those two boundaries: a source-level CPG run can inherit both ordinary
source-backed soundness and per-hop extraction-origin coverage.

Claim boundary:

* Verified here: source-backed CPG runs built from no-orphan CPG adapters are
  sound, and their underlying CPG hops still have checked extraction origins.
* External obligations: real extractors must still prove source/artifact sink
  links and extraction-origin facts are correct.
* Not modeled here: source-map completeness, parser correctness, generated-code
  semantics, real DDG/CDG algorithms, or analyzer recall.
-/

namespace PcSastLean

def sourceBackedNoOrphanCPGRun
    (sourceViolations : List Node)
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (cert : CPGNoOrphanFindingCert)
    (prov : SourceSinkProv) : AnalyzerRun :=
  SourceBackedRun sourceViolations
    (cpgNoOrphanFindingRun nodes components sources sinks cert).concrete
    (cpgNoOrphanFindingRun nodes components sources sinks cert).abstract
    prov

theorem sourceBackedNoOrphanCPGRun_sound
    {sourceViolations : List Node}
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId}
    {cert : CPGNoOrphanFindingCert} {prov : SourceSinkProv}
    (hcert : checkCPGNoOrphanFinding nodes components sources sinks cert = true)
    (hsourceCovered : SourceViolationsCoveredBy sourceViolations prov)
    (hprov : SourceSinkProv.Sound sourceViolations
      (cpgNoOrphanFindingRun nodes components sources sinks cert).concrete prov) :
    (sourceBackedNoOrphanCPGRun
      sourceViolations nodes components sources sinks cert prov).Sound := by
  exact sourceBackedRun_sound
    hsourceCovered
    (cpgNoOrphanFindingRun_sound hcert)
    hprov

theorem sourceBackedNoOrphanCPGRun_hops_have_origins
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId}
    {cert : CPGNoOrphanFindingCert}
    (hcert : checkCPGNoOrphanFinding nodes components sources sinks cert = true) :
    forall hop, hop ∈ cert.finding.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge := by
  exact cpgNoOrphanFindingRun_hops_have_origins hcert

def sourceBackedNoOrphanOrderedSanitizerRun
    (sourceViolations : List Node)
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (components : List CPGComponentEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGNoOrphanOrderedSanitizerCert)
    (prov : SourceSinkProv) : AnalyzerRun :=
  SourceBackedRun sourceViolations
    (cpgNoOrphanOrderedSanitizerRun
      nodes nodeFacts valueFacts components policyRules sanitizerRules query cert).concrete
    (cpgNoOrphanOrderedSanitizerRun
      nodes nodeFacts valueFacts components policyRules sanitizerRules query cert).abstract
    prov

theorem sourceBackedNoOrphanOrderedSanitizerRun_sound
    {sourceViolations : List Node}
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {components : List CPGComponentEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery}
    {cert : CPGNoOrphanOrderedSanitizerCert} {prov : SourceSinkProv}
    (hcert :
      checkCPGNoOrphanOrderedSanitizer
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert = true)
    (hsourceCovered : SourceViolationsCoveredBy sourceViolations prov)
    (hprov : SourceSinkProv.Sound sourceViolations
      (cpgNoOrphanOrderedSanitizerRun
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert).concrete
      prov) :
    (sourceBackedNoOrphanOrderedSanitizerRun
      sourceViolations nodes nodeFacts valueFacts components policyRules
      sanitizerRules query cert prov).Sound := by
  exact sourceBackedRun_sound
    hsourceCovered
    (cpgNoOrphanOrderedSanitizerRun_sound hcert)
    hprov

theorem sourceBackedNoOrphanOrderedSanitizerRun_hops_have_origins
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {components : List CPGComponentEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery}
    {cert : CPGNoOrphanOrderedSanitizerCert}
    (hcert :
      checkCPGNoOrphanOrderedSanitizer
        nodes nodeFacts valueFacts components policyRules sanitizerRules query cert = true) :
    forall hop, hop ∈ cert.ordered.sanitized.policyBacked.finding.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge := by
  exact cpgNoOrphanOrderedSanitizerRun_hops_have_origins hcert

/-! ## Demo: source-level CPG runs inherit no-orphan hop provenance -/

def sourceProvNoOrphanCPG : SourceSinkProv :=
  { sourceSink := 9010
  , artifactSink := cpgNoOrphanFindingCert.finding.sink
  , loc := demoLoc
  }

def sourceNoOrphanCPGViolations : List Node := [9010]

theorem sourceNoOrphanCPGCoveredBy :
    SourceViolationsCoveredBy
      sourceNoOrphanCPGViolations sourceProvNoOrphanCPG := by
  intro sink h
  simp [sourceNoOrphanCPGViolations, sourceProvNoOrphanCPG] at h
  exact h

theorem sourceNoOrphanCPGProvSound :
    SourceSinkProv.Sound sourceNoOrphanCPGViolations
      (cpgNoOrphanFindingRun
        cpgTraversalNodes cpgComponentGraph
        cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
        cpgNoOrphanFindingCert).concrete
      sourceProvNoOrphanCPG := by
  intro _h
  simp [sourceNoOrphanCPGViolations, cpgNoOrphanFindingRun,
    sourceProvNoOrphanCPG, cpgNoOrphanFindingCert, cpgAstCfgDataCert]

def sourceBackedNoOrphanCPGDemoRun : AnalyzerRun :=
  sourceBackedNoOrphanCPGRun
    sourceNoOrphanCPGViolations
    cpgTraversalNodes cpgComponentGraph
    cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
    cpgNoOrphanFindingCert
    sourceProvNoOrphanCPG

example : sourceBackedNoOrphanCPGDemoRun.Sound :=
  sourceBackedNoOrphanCPGRun_sound
    (by native_decide)
    sourceNoOrphanCPGCoveredBy
    sourceNoOrphanCPGProvSound

example :
    forall hop, hop ∈ cpgNoOrphanFindingCert.finding.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge :=
  sourceBackedNoOrphanCPGRun_hops_have_origins
    (nodes := cpgTraversalNodes)
    (components := cpgComponentGraph)
    (sources := cpgAstCfgDataQuery.sources)
    (sinks := cpgAstCfgDataQuery.sinks)
    (cert := cpgNoOrphanFindingCert)
    (by native_decide)

def sourceProvNoOrphanSanitizedCPG : SourceSinkProv :=
  { sourceSink := 9011
  , artifactSink :=
      cpgNoOrphanOrderedSanitizerCert.ordered.sanitized.policyBacked.finding.sink
  , loc := demoLoc
  }

def sourceNoOrphanSanitizedViolations : List Node := []

theorem sourceNoOrphanSanitizedCoveredBy :
    SourceViolationsCoveredBy
      sourceNoOrphanSanitizedViolations sourceProvNoOrphanSanitizedCPG := by
  intro sink h
  simp [sourceNoOrphanSanitizedViolations] at h

theorem sourceNoOrphanSanitizedProvSound :
    SourceSinkProv.Sound sourceNoOrphanSanitizedViolations
      (cpgNoOrphanOrderedSanitizerRun
        cpgTraversalNodes
        cpgSanitizerFacts
        cpgValueFlowFacts
        cpgComponentGraph
        cpgPolicyRules
        cpgSanitizerRules
        cpgNodePredicateQuery
        cpgNoOrphanOrderedSanitizerCert).concrete
      sourceProvNoOrphanSanitizedCPG := by
  intro h
  simp [sourceNoOrphanSanitizedViolations] at h

def sourceBackedNoOrphanSanitizedDemoRun : AnalyzerRun :=
  sourceBackedNoOrphanOrderedSanitizerRun
    sourceNoOrphanSanitizedViolations
    cpgTraversalNodes
    cpgSanitizerFacts
    cpgValueFlowFacts
    cpgComponentGraph
    cpgPolicyRules
    cpgSanitizerRules
    cpgNodePredicateQuery
    cpgNoOrphanOrderedSanitizerCert
    sourceProvNoOrphanSanitizedCPG

example : sourceBackedNoOrphanSanitizedDemoRun.Sound :=
  sourceBackedNoOrphanOrderedSanitizerRun_sound
    (by native_decide)
    sourceNoOrphanSanitizedCoveredBy
    sourceNoOrphanSanitizedProvSound

example :
    forall hop,
      hop ∈
        cpgNoOrphanOrderedSanitizerCert.ordered.sanitized.policyBacked.finding.hops ->
      exists origin : CPGExtractionOrigin,
        hop.kind = origin.componentKind.toEdgeKind /\
        hop.edge = origin.toComponentEdge.toCPGEdge :=
  sourceBackedNoOrphanOrderedSanitizerRun_hops_have_origins
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
