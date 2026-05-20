import PcSastLean.CPGNodePredicates

/-!
CPG source/sink policy provenance.

`CPGNodePredicates` lets a traversal template require source and sink classes,
but those classes were still opaque metadata.  This module adds a small policy
provenance layer: a source/sink class fact is accepted only when it is backed by
a checked call-name fact and a policy rule.

Claim boundary:

* Verified here: accepted policy-backed traversal certificates imply a real CPG
  node-predicate traversal match, and the endpoint source/sink class facts are
  justified by explicit policy rules.
* External obligations: production CPG builders must prove call-name extraction
  and rule generation are faithful to the source program and security policy.
* Not modeled here: string matching, framework-specific source/sink discovery,
  overload resolution, type signatures, receiver dispatch, or sanitizer policy.
-/

namespace PcSastLean

inductive CPGPolicyRule where
  | source (name : CPGName) (cls : SourceClass)
  | sink (name : CPGName) (cls : SinkClass)
deriving DecidableEq, Repr

inductive CPGPolicyFactCert where
  | source (id : CPGId) (name : CPGName) (cls : SourceClass)
  | sink (id : CPGId) (name : CPGName) (cls : SinkClass)
deriving DecidableEq, Repr

def CPGPolicyFactCert.Sound
    (rules : List CPGPolicyRule) (facts : List CPGNodeFact) :
    CPGPolicyFactCert -> Prop
  | CPGPolicyFactCert.source id name cls =>
      CPGPolicyRule.source name cls ∈ rules /\
      CPGNodeFact.callName id name ∈ facts /\
      CPGNodeFact.sourceClass id cls ∈ facts
  | CPGPolicyFactCert.sink id name cls =>
      CPGPolicyRule.sink name cls ∈ rules /\
      CPGNodeFact.callName id name ∈ facts /\
      CPGNodeFact.sinkClass id cls ∈ facts

def checkCPGPolicyFactCert
    (rules : List CPGPolicyRule) (facts : List CPGNodeFact)
    (cert : CPGPolicyFactCert) : Bool :=
  match cert with
  | CPGPolicyFactCert.source id name cls =>
      decide (CPGPolicyRule.source name cls ∈ rules) &&
      decide (CPGNodeFact.callName id name ∈ facts) &&
      decide (CPGNodeFact.sourceClass id cls ∈ facts)
  | CPGPolicyFactCert.sink id name cls =>
      decide (CPGPolicyRule.sink name cls ∈ rules) &&
      decide (CPGNodeFact.callName id name ∈ facts) &&
      decide (CPGNodeFact.sinkClass id cls ∈ facts)

theorem checkCPGPolicyFactCert_sound
    {rules : List CPGPolicyRule} {facts : List CPGNodeFact}
    {cert : CPGPolicyFactCert}
    (h : checkCPGPolicyFactCert rules facts cert = true) :
    cert.Sound rules facts := by
  cases cert with
  | source id name cls =>
      simp [checkCPGPolicyFactCert, CPGPolicyFactCert.Sound] at h
      exact ⟨h.left.left, h.left.right, h.right⟩
  | sink id name cls =>
      simp [checkCPGPolicyFactCert, CPGPolicyFactCert.Sound] at h
      exact ⟨h.left.left, h.left.right, h.right⟩

def SourcePolicyMatches
    (query : CPGNodeQuery) (finding : CPGFindingCert)
    (cert : CPGPolicyFactCert) : Prop :=
  match query.sourcePred, cert with
  | CPGNodePredicate.sourceClassIs expected,
      CPGPolicyFactCert.source id _ cls =>
      id = finding.source /\ cls = expected
  | _, _ => False

def SinkPolicyMatches
    (query : CPGNodeQuery) (finding : CPGFindingCert)
    (cert : CPGPolicyFactCert) : Prop :=
  match query.sinkPred, cert with
  | CPGNodePredicate.sinkClassIs expected,
      CPGPolicyFactCert.sink id _ cls =>
      id = finding.sink /\ cls = expected
  | _, _ => False

def checkSourcePolicyMatches
    (query : CPGNodeQuery) (finding : CPGFindingCert)
    (cert : CPGPolicyFactCert) : Bool :=
  match query.sourcePred, cert with
  | CPGNodePredicate.sourceClassIs expected,
      CPGPolicyFactCert.source id _ cls =>
      decide (id = finding.source) && decide (cls = expected)
  | _, _ => false

def checkSinkPolicyMatches
    (query : CPGNodeQuery) (finding : CPGFindingCert)
    (cert : CPGPolicyFactCert) : Bool :=
  match query.sinkPred, cert with
  | CPGNodePredicate.sinkClassIs expected,
      CPGPolicyFactCert.sink id _ cls =>
      decide (id = finding.sink) && decide (cls = expected)
  | _, _ => false

theorem checkSourcePolicyMatches_sound
    {query : CPGNodeQuery} {finding : CPGFindingCert}
    {cert : CPGPolicyFactCert}
    (h : checkSourcePolicyMatches query finding cert = true) :
    SourcePolicyMatches query finding cert := by
  rcases query with ⟨traversal, sourcePred, sinkPred, hopDstPreds⟩
  cases sourcePred <;> cases cert <;>
    simp [checkSourcePolicyMatches, SourcePolicyMatches] at h ⊢
  exact h

theorem checkSinkPolicyMatches_sound
    {query : CPGNodeQuery} {finding : CPGFindingCert}
    {cert : CPGPolicyFactCert}
    (h : checkSinkPolicyMatches query finding cert = true) :
    SinkPolicyMatches query finding cert := by
  rcases query with ⟨traversal, sourcePred, sinkPred, hopDstPreds⟩
  cases sinkPred <;> cases cert <;>
    simp [checkSinkPolicyMatches, SinkPolicyMatches] at h ⊢
  exact h

structure CPGPolicyBackedTraversalCert where
  finding : CPGFindingCert
  sourcePolicy : CPGPolicyFactCert
  sinkPolicy : CPGPolicyFactCert
deriving Repr

def CPGPolicyBackedTraversalMatch
    (nodes : List CPGNode) (facts : List CPGNodeFact)
    (edges : List CPGEdge) (rules : List CPGPolicyRule)
    (query : CPGNodeQuery) (cert : CPGPolicyBackedTraversalCert) : Prop :=
  CPGNodeTraversalMatch nodes facts edges query cert.finding.source cert.finding.sink /\
  cert.sourcePolicy.Sound rules facts /\
  cert.sinkPolicy.Sound rules facts /\
  SourcePolicyMatches query cert.finding cert.sourcePolicy /\
  SinkPolicyMatches query cert.finding cert.sinkPolicy

def checkCPGPolicyBackedTraversal
    (nodes : List CPGNode) (facts : List CPGNodeFact)
    (edges : List CPGEdge) (rules : List CPGPolicyRule)
    (query : CPGNodeQuery) (cert : CPGPolicyBackedTraversalCert) : Bool :=
  checkCPGNodeTraversal nodes facts edges query cert.finding &&
  checkCPGPolicyFactCert rules facts cert.sourcePolicy &&
  checkCPGPolicyFactCert rules facts cert.sinkPolicy &&
  checkSourcePolicyMatches query cert.finding cert.sourcePolicy &&
  checkSinkPolicyMatches query cert.finding cert.sinkPolicy

theorem checked_cpg_policy_backed_traversal_sound
    {nodes : List CPGNode} {facts : List CPGNodeFact}
    {edges : List CPGEdge} {rules : List CPGPolicyRule}
    {query : CPGNodeQuery} {cert : CPGPolicyBackedTraversalCert}
    (h : checkCPGPolicyBackedTraversal nodes facts edges rules query cert = true) :
    CPGPolicyBackedTraversalMatch nodes facts edges rules query cert := by
  simp [checkCPGPolicyBackedTraversal, CPGPolicyBackedTraversalMatch] at h
  exact ⟨checked_cpg_node_traversal_match_sound h.left.left.left.left,
    checkCPGPolicyFactCert_sound h.left.left.left.right,
    checkCPGPolicyFactCert_sound h.left.left.right,
    checkSourcePolicyMatches_sound h.left.right,
    checkSinkPolicyMatches_sound h.right⟩

theorem checked_cpg_policy_backed_finding_sound
    {nodes : List CPGNode} {facts : List CPGNodeFact}
    {edges : List CPGEdge} {rules : List CPGPolicyRule}
    {query : CPGNodeQuery} {cert : CPGPolicyBackedTraversalCert}
    (h : checkCPGPolicyBackedTraversal nodes facts edges rules query cert = true) :
    CPGFinding edges query.traversal.sources query.traversal.sinks
      cert.finding.source cert.finding.sink := by
  simp [checkCPGPolicyBackedTraversal] at h
  exact checked_cpg_node_traversal_finding_sound h.left.left.left.left

/-! ## Demo: source/sink classes backed by policy rules -/

def cpgPolicyRules : List CPGPolicyRule :=
  [ CPGPolicyRule.source sourceCallName userInputClass
  , CPGPolicyRule.sink sinkCallName commandSinkClass
  ]

def cpgPolicyBackedCert : CPGPolicyBackedTraversalCert :=
  { finding := cpgAstCfgDataCert
  , sourcePolicy :=
      CPGPolicyFactCert.source 10 sourceCallName userInputClass
  , sinkPolicy :=
      CPGPolicyFactCert.sink 13 sinkCallName commandSinkClass
  }

example :
    checkCPGPolicyBackedTraversal
      cpgTraversalNodes
      cpgNodePredicateFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgPolicyRules
      cpgNodePredicateQuery
      cpgPolicyBackedCert = true := by
  native_decide

example :
    CPGPolicyBackedTraversalMatch
      cpgTraversalNodes
      cpgNodePredicateFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgPolicyRules
      cpgNodePredicateQuery
      cpgPolicyBackedCert :=
  checked_cpg_policy_backed_traversal_sound
    (nodes := cpgTraversalNodes)
    (facts := cpgNodePredicateFacts)
    (cert := cpgPolicyBackedCert)
    (by native_decide)

example :
    CPGFinding
      (mergeComponentEdges cpgComponentGraph)
      cpgAstCfgDataQuery.sources
      cpgAstCfgDataQuery.sinks
      10
      13 :=
  checked_cpg_policy_backed_finding_sound
    (nodes := cpgTraversalNodes)
    (facts := cpgNodePredicateFacts)
    (edges := mergeComponentEdges cpgComponentGraph)
    (rules := cpgPolicyRules)
    (query := cpgNodePredicateQuery)
    (cert := cpgPolicyBackedCert)
    (by native_decide)

end PcSastLean
