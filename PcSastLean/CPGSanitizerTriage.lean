import PcSastLean.CPGOrderedSanitizer
import PcSastLean.CIGate

/-!
CPG sanitizer evidence as proof-carrying triage.

`CPGOrderedSanitizer` proves that a sanitizer precedes the sink and carries the
same value token.  This module packages that evidence into the CI triage
interface.  The modeled concrete semantics here is deliberately narrow: the CPG
sink is a concrete vulnerability only when the required ordered sanitizer
evidence is absent.  Under that modeled policy, accepted ordered sanitizer
evidence can suppress the abstract CPG finding without hiding a concrete bug.

Claim boundary:

* Verified here: checked ordered sanitizer evidence can serve as `TriageEvidence`
  for the modeled sanitized-path CPG semantics, and the CI no-bug-hiding theorem
  composes with that evidence.
* External obligations: production systems must prove that this modeled concrete
  sanitized-path semantics corresponds to the real language/framework behavior.
* Not modeled here: dominance, path feasibility, aliases, exceptional control
  flow, or real sanitizer completeness.
-/

namespace PcSastLean

def cpgUnsanitizedConcreteFinding
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (edges : List CPGEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGOrderedSanitizedTraversalCert) : List Node :=
  if checkCPGOrderedSanitizedTraversal
      nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert
    then []
    else [cert.sanitized.policyBacked.finding.sink]

theorem checked_ordered_sanitizer_not_concrete
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGOrderedSanitizedTraversalCert}
    (h :
      checkCPGOrderedSanitizedTraversal
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert = true) :
    cert.sanitized.policyBacked.finding.sink ∉
      cpgUnsanitizedConcreteFinding
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert := by
  simp [cpgUnsanitizedConcreteFinding, h]

def orderedSanitizerTriageEvidence
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (edges : List CPGEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGOrderedSanitizedTraversalCert)
    (_h :
      checkCPGOrderedSanitizedTraversal
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert = true) :
    TriageEvidence :=
  { sink := cert.sanitized.policyBacked.finding.sink
  , impossible :=
      CPGOrderedSanitizedTraversalMatch
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert
  }

theorem orderedSanitizerTriageEvidence_sound
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (edges : List CPGEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGOrderedSanitizedTraversalCert)
    (h :
      checkCPGOrderedSanitizedTraversal
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert = true) :
    EvidenceSound
      (cpgUnsanitizedConcreteFinding
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert)
      (orderedSanitizerTriageEvidence
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert h) := by
  intro _himpossible
  exact checked_ordered_sanitizer_not_concrete h

def orderedSanitizerRun
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (edges : List CPGEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGOrderedSanitizedTraversalCert) : AnalyzerRun :=
  { concrete :=
      cpgUnsanitizedConcreteFinding
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert
  , abstract := [cert.sanitized.policyBacked.finding.sink]
  }

theorem orderedSanitizerRun_sound
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGOrderedSanitizedTraversalCert}
    (h :
      checkCPGOrderedSanitizedTraversal
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert = true) :
    (orderedSanitizerRun
      nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert).Sound := by
  intro sink hconcrete
  simp [orderedSanitizerRun, cpgUnsanitizedConcreteFinding, h] at hconcrete

/-! ## Demo: suppressing a sanitized CPG finding without hiding concrete bugs -/

def orderedSanitizerDemoRun : AnalyzerRun :=
  orderedSanitizerRun
    cpgTraversalNodes
    cpgSanitizerFacts
    cpgValueFlowFacts
    (mergeComponentEdges cpgComponentGraph)
    cpgPolicyRules
    cpgSanitizerRules
    cpgNodePredicateQuery
    cpgOrderedSanitizedTraversalCert

theorem orderedSanitizerDemoRunSound : orderedSanitizerDemoRun.Sound :=
  orderedSanitizerRun_sound (by native_decide)

def orderedSanitizerDemoEvidence : TriageEvidence :=
  orderedSanitizerTriageEvidence
    cpgTraversalNodes
    cpgSanitizerFacts
    cpgValueFlowFacts
    (mergeComponentEdges cpgComponentGraph)
    cpgPolicyRules
    cpgSanitizerRules
    cpgNodePredicateQuery
    cpgOrderedSanitizedTraversalCert
    (by native_decide)

theorem orderedSanitizerDemoEvidenceSound :
    EvidenceSound orderedSanitizerDemoRun.concrete orderedSanitizerDemoEvidence := by
  unfold orderedSanitizerDemoRun orderedSanitizerDemoEvidence
  exact orderedSanitizerTriageEvidence_sound
    cpgTraversalNodes
    cpgSanitizerFacts
    cpgValueFlowFacts
    (mergeComponentEdges cpgComponentGraph)
    cpgPolicyRules
    cpgSanitizerRules
    cpgNodePredicateQuery
    cpgOrderedSanitizedTraversalCert
    (by native_decide)

def orderedSanitizerDemoTriage : TriageRun :=
  { report := []
  , suppressed := [cpgOrderedSanitizedTraversalCert.sanitized.policyBacked.finding.sink]
  , evidence := [orderedSanitizerDemoEvidence]
  }

theorem orderedSanitizerDemoTriageComplete :
    orderedSanitizerDemoTriage.Complete orderedSanitizerDemoRun := by
  intro sink habs
  right
  have hsink :
      sink = cpgOrderedSanitizedTraversalCert.sanitized.policyBacked.finding.sink := by
    simpa [orderedSanitizerDemoRun, orderedSanitizerRun] using habs
  subst hsink
  constructor
  · simp [orderedSanitizerDemoTriage]
  · refine ⟨orderedSanitizerDemoEvidence, ?_, ?_, ?_, ?_⟩
    · simp [orderedSanitizerDemoTriage]
    · simp [orderedSanitizerDemoEvidence, orderedSanitizerTriageEvidence]
    · exact checked_cpg_ordered_sanitized_traversal_sound (by native_decide)
    · exact orderedSanitizerDemoEvidenceSound

example : ListSubset orderedSanitizerDemoRun.concrete orderedSanitizerDemoTriage.report :=
  ci_gate_no_bug_hiding
    orderedSanitizerDemoRunSound
    orderedSanitizerDemoTriageComplete

example :
    cpgOrderedSanitizedTraversalCert.sanitized.policyBacked.finding.sink ∉
      orderedSanitizerDemoRun.concrete :=
  ci_gate_not_reported_not_concrete
    orderedSanitizerDemoRunSound
    orderedSanitizerDemoTriageComplete
    (by simp [orderedSanitizerDemoTriage])

end PcSastLean
