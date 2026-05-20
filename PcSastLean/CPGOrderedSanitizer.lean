import PcSastLean.CPGSanitizerPolicy

/-!
Ordered and value-carrying CPG sanitizer evidence.

`CPGSanitizerPolicy` proves that a sanitizer node exists somewhere on a finding
path and grants the sink's required `SinkKind`.  This module strengthens that
evidence: the sanitizer must occur before the sink, and the sanitizer output and
sink input must share a checked flow token.

Claim boundary:

* Verified here: accepted ordered sanitizer certificates prove the sanitizer node
  occurs before the sink on the CPG hop-destination path, carries the same value
  token to the sink, and grants the required sanitizer-lattice protection.
* External obligations: production CPG builders must prove that flow tokens
  faithfully represent value identity through assignments, calls, aliases, and
  sanitizers.
* Not modeled here: alias-sensitive value identity, dominance, loops, path
  quantification, multi-argument sanitizers, or partial sanitization.
-/

namespace PcSastLean

abbrev FlowToken := Nat

inductive CPGValueFlowFact where
  | sanitizerOutput (id : CPGId) (token : FlowToken)
  | sinkInput (id : CPGId) (token : FlowToken)
deriving DecidableEq, Repr

def BeforeInList (before after : CPGId) : List CPGId -> Prop
  | [] => False
  | x :: rest =>
      if x = before then after ∈ rest else BeforeInList before after rest

def checkBeforeInList (before after : CPGId) : List CPGId -> Bool
  | [] => false
  | x :: rest =>
      if x = before then decide (after ∈ rest)
      else checkBeforeInList before after rest

theorem checkBeforeInList_sound
    {before after : CPGId} :
    forall xs,
      checkBeforeInList before after xs = true ->
      BeforeInList before after xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      simp [checkBeforeInList] at h
  | cons x rest ih =>
      intro h
      by_cases hx : x = before
      · simp [checkBeforeInList, BeforeInList, hx] at h ⊢
        exact h
      · simp [checkBeforeInList, BeforeInList, hx] at h ⊢
        exact ih h

def OrderedSanitizerCoversFinding
    (finding : CPGFindingCert) (cert : CPGSanitizerFactCert)
    (kind : SinkKind) : Prop :=
  match cert with
  | CPGSanitizerFactCert.sanitizer id _ got =>
      BeforeInList id finding.sink (cpgHopDsts finding.hops) /\ got = kind

def checkOrderedSanitizerCoversFinding
    (finding : CPGFindingCert) (cert : CPGSanitizerFactCert)
    (kind : SinkKind) : Bool :=
  match cert with
  | CPGSanitizerFactCert.sanitizer id _ got =>
      checkBeforeInList id finding.sink (cpgHopDsts finding.hops) &&
      decide (got = kind)

theorem checkOrderedSanitizerCoversFinding_sound
    {finding : CPGFindingCert} {cert : CPGSanitizerFactCert}
    {kind : SinkKind}
    (h : checkOrderedSanitizerCoversFinding finding cert kind = true) :
    OrderedSanitizerCoversFinding finding cert kind := by
  cases cert with
  | sanitizer id name got =>
      simp [checkOrderedSanitizerCoversFinding, OrderedSanitizerCoversFinding] at h
      exact ⟨checkBeforeInList_sound (cpgHopDsts finding.hops) h.left, h.right⟩

def ValueTokenCarriesSanitizedFlow
    (facts : List CPGValueFlowFact)
    (finding : CPGFindingCert) (cert : CPGSanitizerFactCert)
    (token : FlowToken) : Prop :=
  match cert with
  | CPGSanitizerFactCert.sanitizer id _ _ =>
      CPGValueFlowFact.sanitizerOutput id token ∈ facts /\
      CPGValueFlowFact.sinkInput finding.sink token ∈ facts

def checkValueTokenCarriesSanitizedFlow
    (facts : List CPGValueFlowFact)
    (finding : CPGFindingCert) (cert : CPGSanitizerFactCert)
    (token : FlowToken) : Bool :=
  match cert with
  | CPGSanitizerFactCert.sanitizer id _ _ =>
      decide (CPGValueFlowFact.sanitizerOutput id token ∈ facts) &&
      decide (CPGValueFlowFact.sinkInput finding.sink token ∈ facts)

theorem checkValueTokenCarriesSanitizedFlow_sound
    {facts : List CPGValueFlowFact} {finding : CPGFindingCert}
    {cert : CPGSanitizerFactCert} {token : FlowToken}
    (h :
      checkValueTokenCarriesSanitizedFlow facts finding cert token = true) :
    ValueTokenCarriesSanitizedFlow facts finding cert token := by
  cases cert with
  | sanitizer id name kind =>
      simp [checkValueTokenCarriesSanitizedFlow,
        ValueTokenCarriesSanitizedFlow] at h
      exact h

structure CPGOrderedSanitizedTraversalCert where
  sanitized : CPGSanitizedTraversalCert
  token : FlowToken
deriving Repr

def CPGOrderedSanitizedTraversalMatch
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (edges : List CPGEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGOrderedSanitizedTraversalCert) : Prop :=
  CPGSanitizedTraversalMatch
    nodes nodeFacts edges policyRules sanitizerRules query cert.sanitized /\
  OrderedSanitizerCoversFinding
    cert.sanitized.policyBacked.finding
    cert.sanitized.sanitizer
    cert.sanitized.required /\
  ValueTokenCarriesSanitizedFlow
    valueFacts
    cert.sanitized.policyBacked.finding
    cert.sanitized.sanitizer
    cert.token

def checkCPGOrderedSanitizedTraversal
    (nodes : List CPGNode) (nodeFacts : List CPGNodeFact)
    (valueFacts : List CPGValueFlowFact)
    (edges : List CPGEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery)
    (cert : CPGOrderedSanitizedTraversalCert) : Bool :=
  checkCPGSanitizedTraversal
    nodes nodeFacts edges policyRules sanitizerRules query cert.sanitized &&
  checkOrderedSanitizerCoversFinding
    cert.sanitized.policyBacked.finding
    cert.sanitized.sanitizer
    cert.sanitized.required &&
  checkValueTokenCarriesSanitizedFlow
    valueFacts
    cert.sanitized.policyBacked.finding
    cert.sanitized.sanitizer
    cert.token

theorem checked_cpg_ordered_sanitized_traversal_sound
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGOrderedSanitizedTraversalCert}
    (h :
      checkCPGOrderedSanitizedTraversal
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert = true) :
    CPGOrderedSanitizedTraversalMatch
      nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert := by
  simp [checkCPGOrderedSanitizedTraversal,
    CPGOrderedSanitizedTraversalMatch] at h
  exact ⟨checked_cpg_sanitized_traversal_sound h.left.left,
    checkOrderedSanitizerCoversFinding_sound h.left.right,
    checkValueTokenCarriesSanitizedFlow_sound h.right⟩

theorem checked_cpg_ordered_sanitized_finding_sound
    {nodes : List CPGNode} {nodeFacts : List CPGNodeFact}
    {valueFacts : List CPGValueFlowFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGOrderedSanitizedTraversalCert}
    (h :
      checkCPGOrderedSanitizedTraversal
        nodes nodeFacts valueFacts edges policyRules sanitizerRules query cert = true) :
    CPGFinding edges query.traversal.sources query.traversal.sinks
      cert.sanitized.policyBacked.finding.source
      cert.sanitized.policyBacked.finding.sink := by
  simp [checkCPGOrderedSanitizedTraversal] at h
  exact checked_cpg_sanitized_finding_sound h.left.left

/-! ## Demo: sanitizer precedes sink and carries the same value token -/

def cpgSanitizedToken : FlowToken := 42

def cpgValueFlowFacts : List CPGValueFlowFact :=
  [ CPGValueFlowFact.sanitizerOutput 12 cpgSanitizedToken
  , CPGValueFlowFact.sinkInput 13 cpgSanitizedToken
  ]

def cpgOrderedSanitizedTraversalCert : CPGOrderedSanitizedTraversalCert :=
  { sanitized := cpgSanitizedTraversalCert
  , token := cpgSanitizedToken
  }

example :
    checkBeforeInList 12 13 (cpgHopDsts cpgAstCfgDataCert.hops) = true := by
  native_decide

example :
    checkCPGOrderedSanitizedTraversal
      cpgTraversalNodes
      cpgSanitizerFacts
      cpgValueFlowFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgPolicyRules
      cpgSanitizerRules
      cpgNodePredicateQuery
      cpgOrderedSanitizedTraversalCert = true := by
  native_decide

example :
    CPGOrderedSanitizedTraversalMatch
      cpgTraversalNodes
      cpgSanitizerFacts
      cpgValueFlowFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgPolicyRules
      cpgSanitizerRules
      cpgNodePredicateQuery
      cpgOrderedSanitizedTraversalCert :=
  checked_cpg_ordered_sanitized_traversal_sound
    (nodes := cpgTraversalNodes)
    (nodeFacts := cpgSanitizerFacts)
    (valueFacts := cpgValueFlowFacts)
    (cert := cpgOrderedSanitizedTraversalCert)
    (by native_decide)

example :
    CPGFinding
      (mergeComponentEdges cpgComponentGraph)
      cpgAstCfgDataQuery.sources
      cpgAstCfgDataQuery.sinks
      10
      13 :=
  checked_cpg_ordered_sanitized_finding_sound
    (nodes := cpgTraversalNodes)
    (nodeFacts := cpgSanitizerFacts)
    (valueFacts := cpgValueFlowFacts)
    (edges := mergeComponentEdges cpgComponentGraph)
    (policyRules := cpgPolicyRules)
    (sanitizerRules := cpgSanitizerRules)
    (query := cpgNodePredicateQuery)
    (cert := cpgOrderedSanitizedTraversalCert)
    (by native_decide)

end PcSastLean
