import PcSastLean.CPGPolicyProvenance
import PcSastLean.SanitizerLattice

/-!
CPG sanitizer policy provenance.

Source/sink policy provenance explains why endpoint nodes are sources and sinks.
The next question is whether an intermediate sanitizer node protects the flow for
the sink's required context.  This module connects CPG node facts to the
context-sensitive `SanitizerLattice`: a sanitizer call-name policy grants exactly
one `SinkKind` protection, and a sink class policy declares which `SinkKind` a
sink requires.

Claim boundary:

* Verified here: accepted sanitizer-policy certificates identify a sanitizer
  node on the CPG path, tie it to a sanitizer rule, tie the sink class to a
  required `SinkKind`, and prove the sanitizer grants that protection in the
  sanitizer lattice.
* External obligations: production CPG builders must prove call-name extraction,
  path ordering, and sanitizer-policy compilation are faithful.
* Not modeled here: parser-state sanitizers, multi-argument sanitizers, partial
  sanitization, dominance/order constraints, aliasing through the sanitized
  value, or composed sanitizer policies.
-/

namespace PcSastLean

inductive CPGSanitizerPolicyRule where
  | sanitizer (name : CPGName) (kind : SinkKind)
  | sinkRequires (cls : SinkClass) (kind : SinkKind)
deriving DecidableEq, Repr

inductive CPGSanitizerFactCert where
  | sanitizer (id : CPGId) (name : CPGName) (kind : SinkKind)
deriving DecidableEq, Repr

def CPGSanitizerFactCert.Sound
    (rules : List CPGSanitizerPolicyRule) (facts : List CPGNodeFact) :
    CPGSanitizerFactCert -> Prop
  | CPGSanitizerFactCert.sanitizer id name kind =>
      CPGSanitizerPolicyRule.sanitizer name kind ∈ rules /\
      CPGNodeFact.callName id name ∈ facts

def checkCPGSanitizerFactCert
    (rules : List CPGSanitizerPolicyRule) (facts : List CPGNodeFact)
    (cert : CPGSanitizerFactCert) : Bool :=
  match cert with
  | CPGSanitizerFactCert.sanitizer id name kind =>
      decide (CPGSanitizerPolicyRule.sanitizer name kind ∈ rules) &&
      decide (CPGNodeFact.callName id name ∈ facts)

theorem checkCPGSanitizerFactCert_sound
    {rules : List CPGSanitizerPolicyRule} {facts : List CPGNodeFact}
    {cert : CPGSanitizerFactCert}
    (h : checkCPGSanitizerFactCert rules facts cert = true) :
    cert.Sound rules facts := by
  cases cert with
  | sanitizer id name kind =>
      simp [checkCPGSanitizerFactCert, CPGSanitizerFactCert.Sound] at h
      exact h

def SinkPolicyRequires
    (rules : List CPGSanitizerPolicyRule)
    (sinkPolicy : CPGPolicyFactCert) (kind : SinkKind) : Prop :=
  match sinkPolicy with
  | CPGPolicyFactCert.sink _ _ cls =>
      CPGSanitizerPolicyRule.sinkRequires cls kind ∈ rules
  | _ => False

def checkSinkPolicyRequires
    (rules : List CPGSanitizerPolicyRule)
    (sinkPolicy : CPGPolicyFactCert) (kind : SinkKind) : Bool :=
  match sinkPolicy with
  | CPGPolicyFactCert.sink _ _ cls =>
      decide (CPGSanitizerPolicyRule.sinkRequires cls kind ∈ rules)
  | _ => false

theorem checkSinkPolicyRequires_sound
    {rules : List CPGSanitizerPolicyRule}
    {sinkPolicy : CPGPolicyFactCert} {kind : SinkKind}
    (h : checkSinkPolicyRequires rules sinkPolicy kind = true) :
    SinkPolicyRequires rules sinkPolicy kind := by
  cases sinkPolicy <;> simp [checkSinkPolicyRequires, SinkPolicyRequires] at h ⊢
  exact h

def cpgHopDsts : List CPGHop -> List CPGId
  | [] => []
  | hop :: rest => hop.dst :: cpgHopDsts rest

def SanitizerCoversFinding
    (finding : CPGFindingCert) (cert : CPGSanitizerFactCert)
    (kind : SinkKind) : Prop :=
  match cert with
  | CPGSanitizerFactCert.sanitizer id _ got =>
      id ∈ cpgHopDsts finding.hops /\ got = kind

def checkSanitizerCoversFinding
    (finding : CPGFindingCert) (cert : CPGSanitizerFactCert)
    (kind : SinkKind) : Bool :=
  match cert with
  | CPGSanitizerFactCert.sanitizer id _ got =>
      decide (id ∈ cpgHopDsts finding.hops) && decide (got = kind)

theorem checkSanitizerCoversFinding_sound
    {finding : CPGFindingCert} {cert : CPGSanitizerFactCert}
    {kind : SinkKind}
    (h : checkSanitizerCoversFinding finding cert kind = true) :
    SanitizerCoversFinding finding cert kind := by
  cases cert with
  | sanitizer id name got =>
      simp [checkSanitizerCoversFinding, SanitizerCoversFinding] at h
      exact h

theorem cpg_sanitizer_grants_required_protection
    (label : SecLabel) (kind : SinkKind) :
    (SecLabel.sanitize label kind).safeFor kind :=
  SecLabel.sanitize_safe_for label kind

structure CPGSanitizedTraversalCert where
  policyBacked : CPGPolicyBackedTraversalCert
  sanitizer : CPGSanitizerFactCert
  required : SinkKind
deriving Repr

def CPGSanitizedTraversalMatch
    (nodes : List CPGNode) (facts : List CPGNodeFact)
    (edges : List CPGEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery) (cert : CPGSanitizedTraversalCert) : Prop :=
  CPGPolicyBackedTraversalMatch
    nodes facts edges policyRules query cert.policyBacked /\
  cert.sanitizer.Sound sanitizerRules facts /\
  SinkPolicyRequires sanitizerRules cert.policyBacked.sinkPolicy cert.required /\
  SanitizerCoversFinding cert.policyBacked.finding cert.sanitizer cert.required /\
  (SecLabel.sanitize SecLabel.input cert.required).safeFor cert.required

def checkCPGSanitizedTraversal
    (nodes : List CPGNode) (facts : List CPGNodeFact)
    (edges : List CPGEdge) (policyRules : List CPGPolicyRule)
    (sanitizerRules : List CPGSanitizerPolicyRule)
    (query : CPGNodeQuery) (cert : CPGSanitizedTraversalCert) : Bool :=
  checkCPGPolicyBackedTraversal
    nodes facts edges policyRules query cert.policyBacked &&
  checkCPGSanitizerFactCert sanitizerRules facts cert.sanitizer &&
  checkSinkPolicyRequires
    sanitizerRules cert.policyBacked.sinkPolicy cert.required &&
  checkSanitizerCoversFinding
    cert.policyBacked.finding cert.sanitizer cert.required

theorem checked_cpg_sanitized_traversal_sound
    {nodes : List CPGNode} {facts : List CPGNodeFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGSanitizedTraversalCert}
    (h :
      checkCPGSanitizedTraversal
        nodes facts edges policyRules sanitizerRules query cert = true) :
    CPGSanitizedTraversalMatch
      nodes facts edges policyRules sanitizerRules query cert := by
  simp [checkCPGSanitizedTraversal, CPGSanitizedTraversalMatch] at h
  exact ⟨checked_cpg_policy_backed_traversal_sound h.left.left.left,
    checkCPGSanitizerFactCert_sound h.left.left.right,
    checkSinkPolicyRequires_sound h.left.right,
    checkSanitizerCoversFinding_sound h.right,
    cpg_sanitizer_grants_required_protection SecLabel.input cert.required⟩

theorem checked_cpg_sanitized_finding_sound
    {nodes : List CPGNode} {facts : List CPGNodeFact}
    {edges : List CPGEdge} {policyRules : List CPGPolicyRule}
    {sanitizerRules : List CPGSanitizerPolicyRule}
    {query : CPGNodeQuery} {cert : CPGSanitizedTraversalCert}
    (h :
      checkCPGSanitizedTraversal
        nodes facts edges policyRules sanitizerRules query cert = true) :
    CPGFinding edges query.traversal.sources query.traversal.sinks
      cert.policyBacked.finding.source cert.policyBacked.finding.sink := by
  simp [checkCPGSanitizedTraversal] at h
  exact checked_cpg_policy_backed_finding_sound h.left.left.left

/-! ## Demo: sanitizer node protects the command sink class -/

def sanitizerCallName : CPGName := 300

def cpgSanitizerFacts : List CPGNodeFact :=
  CPGNodeFact.callName 12 sanitizerCallName :: cpgNodePredicateFacts

def cpgSanitizerRules : List CPGSanitizerPolicyRule :=
  [ CPGSanitizerPolicyRule.sanitizer sanitizerCallName SinkKind.shell
  , CPGSanitizerPolicyRule.sinkRequires commandSinkClass SinkKind.shell
  ]

def cpgSanitizedTraversalCert : CPGSanitizedTraversalCert :=
  { policyBacked :=
      { finding := cpgAstCfgDataCert
      , sourcePolicy :=
          CPGPolicyFactCert.source 10 sourceCallName userInputClass
      , sinkPolicy :=
          CPGPolicyFactCert.sink 13 sinkCallName commandSinkClass
      }
  , sanitizer :=
      CPGSanitizerFactCert.sanitizer 12 sanitizerCallName SinkKind.shell
  , required := SinkKind.shell
  }

example :
    checkCPGSanitizedTraversal
      cpgTraversalNodes
      cpgSanitizerFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgPolicyRules
      cpgSanitizerRules
      cpgNodePredicateQuery
      cpgSanitizedTraversalCert = true := by
  native_decide

example :
    CPGSanitizedTraversalMatch
      cpgTraversalNodes
      cpgSanitizerFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgPolicyRules
      cpgSanitizerRules
      cpgNodePredicateQuery
      cpgSanitizedTraversalCert :=
  checked_cpg_sanitized_traversal_sound
    (nodes := cpgTraversalNodes)
    (facts := cpgSanitizerFacts)
    (cert := cpgSanitizedTraversalCert)
    (by native_decide)

example :
    (SecLabel.sanitize SecLabel.input SinkKind.shell).safeFor SinkKind.shell :=
  cpg_sanitizer_grants_required_protection SecLabel.input SinkKind.shell

example :
    CPGFinding
      (mergeComponentEdges cpgComponentGraph)
      cpgAstCfgDataQuery.sources
      cpgAstCfgDataQuery.sinks
      10
      13 :=
  checked_cpg_sanitized_finding_sound
    (nodes := cpgTraversalNodes)
    (facts := cpgSanitizerFacts)
    (edges := mergeComponentEdges cpgComponentGraph)
    (policyRules := cpgPolicyRules)
    (sanitizerRules := cpgSanitizerRules)
    (query := cpgNodePredicateQuery)
    (cert := cpgSanitizedTraversalCert)
    (by native_decide)

end PcSastLean
