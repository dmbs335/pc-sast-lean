import PcSastLean.CPGSanitizerTriage

/-!
CPG sanitizer guardrails.

`CPGSanitizerPolicy` and `CPGOrderedSanitizer` already require a sanitizer
certificate to name a `SinkKind`.  This module makes the negative result
explicit: a sanitizer whose kind differs from the sink's required kind cannot be
accepted by the CPG sanitizer checker, and therefore cannot become
proof-carrying triage evidence.

Claim boundary:

* Verified here: accepted CPG sanitizer certificates force the sanitizer kind to
  equal the sink-required kind; wrong-context sanitizer evidence is rejected.
* External obligations: production CPG builders still have to prove call names,
  sink-class policies, path order, and value-flow tokens are extracted
  faithfully.
* Not modeled here: sanitizer parser states, composed sanitizers, sanitizer
  argument semantics, aliases, dominance, exceptional paths, or framework
  callbacks.
-/

namespace PcSastLean

def sanitizerCertKind : CPGSanitizerFactCert -> SinkKind
  | CPGSanitizerFactCert.sanitizer _ _ kind => kind

def sanitizerCertNode : CPGSanitizerFactCert -> CPGId
  | CPGSanitizerFactCert.sanitizer id _ _ => id

theorem wrong_context_sanitizer_does_not_prove_safe
    {got need : SinkKind} (hwrong : Not (got = need)) :
    Not ((SecLabel.sanitize SecLabel.input got).safeFor need) := by
  intro hsafe
  cases got <;> cases need <;>
    simp [SecLabel.sanitize, SecLabel.safeFor, SecLabel.input,
      Protection.add, Protection.has] at hsafe
  all_goals first
    | exact hwrong rfl
    | cases hsafe

theorem checked_sanitizer_kind_matches_required
    {nodes : List CPGNode} {facts : List CPGNodeFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGSanitizedTraversalCert}
    (h :
      checkCPGSanitizedTraversal
        nodes facts edges policyRules sanitizerRules query cert = true) :
    sanitizerCertKind cert.sanitizer = cert.required := by
  have hmatch := checked_cpg_sanitized_traversal_sound h
  rcases hmatch with ⟨_hpolicy, _hsanitizer, _hrequires, hcover, _hsafe⟩
  cases cert with
  | mk policyBacked sanitizer required =>
      cases sanitizer with
      | sanitizer id name got =>
          simpa [sanitizerCertKind] using hcover.right

theorem wrong_context_sanitized_traversal_rejected
    {nodes : List CPGNode} {facts : List CPGNodeFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGSanitizedTraversalCert}
    (hwrong : Not (sanitizerCertKind cert.sanitizer = cert.required)) :
    Not
      (checkCPGSanitizedTraversal
        nodes facts edges policyRules sanitizerRules query cert = true) := by
  intro hcheck
  exact hwrong (checked_sanitizer_kind_matches_required hcheck)

theorem checked_ordered_sanitizer_kind_matches_required
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGOrderedSanitizedTraversalCert}
    (h :
      checkCPGOrderedSanitizedTraversal
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert = true) :
    sanitizerCertKind cert.sanitized.sanitizer = cert.sanitized.required := by
  have hmatch := checked_cpg_ordered_sanitized_traversal_sound h
  rcases hmatch with ⟨_hbase, hordered, _hvalue⟩
  cases cert with
  | mk sanitized token =>
      cases sanitized with
      | mk policyBacked sanitizer required =>
          cases sanitizer with
          | sanitizer id name got =>
              simpa [sanitizerCertKind] using hordered.right

theorem wrong_context_ordered_sanitizer_rejected
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGOrderedSanitizedTraversalCert}
    (hwrong :
      Not (sanitizerCertKind cert.sanitized.sanitizer = cert.sanitized.required)) :
    Not
      (checkCPGOrderedSanitizedTraversal
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert = true) := by
  intro hcheck
  exact hwrong (checked_ordered_sanitizer_kind_matches_required hcheck)

def cpgWrongContextSanitizerRules : List CPGSanitizerPolicyRule :=
  [ CPGSanitizerPolicyRule.sanitizer sanitizerCallName SinkKind.sql
  , CPGSanitizerPolicyRule.sinkRequires commandSinkClass SinkKind.shell
  ]

def cpgWrongContextSanitizedTraversalCert : CPGSanitizedTraversalCert :=
  { policyBacked := cpgSanitizedTraversalCert.policyBacked
  , sanitizer := CPGSanitizerFactCert.sanitizer 12 sanitizerCallName SinkKind.sql
  , required := SinkKind.shell
  }

def cpgWrongContextOrderedSanitizedTraversalCert :
    CPGOrderedSanitizedTraversalCert :=
  { sanitized := cpgWrongContextSanitizedTraversalCert
  , token := cpgSanitizedToken
  }

example :
    Not
      ((SecLabel.sanitize SecLabel.input SinkKind.sql).safeFor
        SinkKind.shell) :=
  wrong_context_sanitizer_does_not_prove_safe (by intro h; cases h)

example :
    checkCPGSanitizedTraversal
      cpgTraversalNodes
      cpgSanitizerFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgPolicyRules
      cpgWrongContextSanitizerRules
      cpgNodePredicateQuery
      cpgWrongContextSanitizedTraversalCert = false := by
  native_decide

example :
    Not
      (checkCPGSanitizedTraversal
        cpgTraversalNodes
        cpgSanitizerFacts
        (mergeComponentEdges cpgComponentGraph)
        cpgPolicyRules
        cpgWrongContextSanitizerRules
        cpgNodePredicateQuery
        cpgWrongContextSanitizedTraversalCert = true) :=
  wrong_context_sanitized_traversal_rejected (by intro h; cases h)

example :
    checkCPGOrderedSanitizedTraversal
      cpgTraversalNodes
      cpgSanitizerFacts
      cpgValueFlowFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgPolicyRules
      cpgWrongContextSanitizerRules
      cpgNodePredicateQuery
      cpgWrongContextOrderedSanitizedTraversalCert = false := by
  native_decide

example :
    Not
      (checkCPGOrderedSanitizedTraversal
        cpgTraversalNodes
        cpgSanitizerFacts
        cpgValueFlowFacts
        (mergeComponentEdges cpgComponentGraph)
        cpgPolicyRules
        cpgWrongContextSanitizerRules
        cpgNodePredicateQuery
        cpgWrongContextOrderedSanitizedTraversalCert = true) :=
  wrong_context_ordered_sanitizer_rejected (by intro h; cases h)

end PcSastLean
