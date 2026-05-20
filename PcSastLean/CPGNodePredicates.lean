import PcSastLean.CPGTraversal

/-!
CPG node predicates for traversal templates.

Edge-kind filters make CPG traversal certificates less arbitrary, but real SAST
queries also depend on node properties: call names, source/sink classifications,
and argument positions.  This module adds a small property layer without changing
the core CPG node type.  A query can require checked facts about its source,
sink, and intermediate path nodes.

Claim boundary:

* Verified here: accepted node-predicate traversal certificates are real CPG
  traversal matches whose endpoints and hops satisfy the requested node facts.
* External obligations: production CPG builders must justify that emitted node
  facts reflect the parsed source program and framework/security policy.
* Not modeled here: strings, types, full AST properties, value numbering,
  alias-aware argument binding, variadic calls, overload resolution, or query
  compilation from CodeQL/Joern.
-/

namespace PcSastLean

abbrev CPGName := Nat
abbrev ArgIndex := Nat
abbrev SourceClass := Nat
abbrev SinkClass := Nat

inductive CPGNodeFact where
  | callName (id : CPGId) (name : CPGName)
  | argumentIndex (id : CPGId) (index : ArgIndex)
  | sourceClass (id : CPGId) (cls : SourceClass)
  | sinkClass (id : CPGId) (cls : SinkClass)
deriving DecidableEq, Repr

inductive CPGNodePredicate where
  | any
  | kindIs (kind : CPGNodeKind)
  | callNameIs (name : CPGName)
  | argumentIndexIs (index : ArgIndex)
  | sourceClassIs (cls : SourceClass)
  | sinkClassIs (cls : SinkClass)
deriving DecidableEq, Repr

def lookupCPGNode (nodes : List CPGNode) (id : CPGId) : Option CPGNode :=
  nodes.find? (fun n => n.id = id)

def CPGNodePredicate.Holds
    (nodes : List CPGNode) (facts : List CPGNodeFact)
    (id : CPGId) : CPGNodePredicate -> Prop
  | CPGNodePredicate.any => HasNode nodes id
  | CPGNodePredicate.kindIs kind =>
      exists n, n ∈ nodes /\ n.id = id /\ n.kind = kind
  | CPGNodePredicate.callNameIs name =>
      CPGNodeFact.callName id name ∈ facts
  | CPGNodePredicate.argumentIndexIs index =>
      CPGNodeFact.argumentIndex id index ∈ facts
  | CPGNodePredicate.sourceClassIs cls =>
      CPGNodeFact.sourceClass id cls ∈ facts
  | CPGNodePredicate.sinkClassIs cls =>
      CPGNodeFact.sinkClass id cls ∈ facts

def checkCPGNodePredicate
    (nodes : List CPGNode) (facts : List CPGNodeFact)
    (id : CPGId) (pred : CPGNodePredicate) : Bool :=
  match pred with
  | CPGNodePredicate.any => checkHasNode nodes id
  | CPGNodePredicate.kindIs kind =>
      match lookupCPGNode nodes id with
      | some n => decide (n.kind = kind)
      | none => false
  | CPGNodePredicate.callNameIs name =>
      decide (CPGNodeFact.callName id name ∈ facts)
  | CPGNodePredicate.argumentIndexIs index =>
      decide (CPGNodeFact.argumentIndex id index ∈ facts)
  | CPGNodePredicate.sourceClassIs cls =>
      decide (CPGNodeFact.sourceClass id cls ∈ facts)
  | CPGNodePredicate.sinkClassIs cls =>
      decide (CPGNodeFact.sinkClass id cls ∈ facts)

theorem lookupCPGNode_some_sound
    {nodes : List CPGNode} {id : CPGId} {n : CPGNode}
    (h : lookupCPGNode nodes id = some n) :
    n ∈ nodes /\ n.id = id := by
  induction nodes with
  | nil =>
      simp [lookupCPGNode] at h
  | cons head rest ih =>
      by_cases hid : head.id = id
      · simp [lookupCPGNode, hid] at h
        subst h
        exact ⟨by simp, hid⟩
      · simp [lookupCPGNode, hid] at h
        have hrest := ih h
        exact ⟨by simp [hrest.left], hrest.right⟩

theorem checkCPGNodePredicate_sound
    {nodes : List CPGNode} {facts : List CPGNodeFact}
    {id : CPGId} {pred : CPGNodePredicate}
    (h : checkCPGNodePredicate nodes facts id pred = true) :
    pred.Holds nodes facts id := by
  cases pred with
  | any =>
      exact checkHasNode_sound h
  | kindIs kind =>
      simp [checkCPGNodePredicate] at h
      cases hlookup : lookupCPGNode nodes id with
      | none =>
          simp [hlookup] at h
      | some n =>
          simp [hlookup] at h
          have hn := lookupCPGNode_some_sound hlookup
          exact ⟨n, hn.left, hn.right, h⟩
  | callNameIs name =>
      simp [checkCPGNodePredicate, CPGNodePredicate.Holds] at h
      exact h
  | argumentIndexIs index =>
      simp [checkCPGNodePredicate, CPGNodePredicate.Holds] at h
      exact h
  | sourceClassIs cls =>
      simp [checkCPGNodePredicate, CPGNodePredicate.Holds] at h
      exact h
  | sinkClassIs cls =>
      simp [checkCPGNodePredicate, CPGNodePredicate.Holds] at h
      exact h

def cpgHopNodePredicatesHold
    (nodes : List CPGNode) (facts : List CPGNodeFact) :
    List CPGHop -> List CPGNodePredicate -> Prop
  | [], [] => True
  | hop :: restHops, pred :: restPreds =>
      pred.Holds nodes facts hop.dst /\
      cpgHopNodePredicatesHold nodes facts restHops restPreds
  | _, _ => False

def checkCPGHopNodePredicates
    (nodes : List CPGNode) (facts : List CPGNodeFact) :
    List CPGHop -> List CPGNodePredicate -> Bool
  | [], [] => true
  | hop :: restHops, pred :: restPreds =>
      checkCPGNodePredicate nodes facts hop.dst pred &&
      checkCPGHopNodePredicates nodes facts restHops restPreds
  | _, _ => false

theorem checkCPGHopNodePredicates_sound
    {nodes : List CPGNode} {facts : List CPGNodeFact} :
    forall hops preds,
      checkCPGHopNodePredicates nodes facts hops preds = true ->
      cpgHopNodePredicatesHold nodes facts hops preds := by
  intro hops
  induction hops with
  | nil =>
      intro preds h
      cases preds with
      | nil =>
          trivial
      | cons _ _ =>
          simp [checkCPGHopNodePredicates] at h
  | cons hop rest ih =>
      intro preds h
      cases preds with
      | nil =>
          simp [checkCPGHopNodePredicates] at h
      | cons pred restPreds =>
          simp [checkCPGHopNodePredicates, cpgHopNodePredicatesHold] at h ⊢
          exact ⟨checkCPGNodePredicate_sound h.left, ih restPreds h.right⟩

structure CPGNodeQuery where
  traversal : CPGTraversalQuery
  sourcePred : CPGNodePredicate
  sinkPred : CPGNodePredicate
  hopDstPreds : List CPGNodePredicate
deriving Repr

def CPGNodeTraversalMatch
    (nodes : List CPGNode) (facts : List CPGNodeFact) (edges : List CPGEdge)
    (query : CPGNodeQuery) (source sink : CPGId) : Prop :=
  CPGTraversalMatch edges query.traversal source sink /\
  query.sourcePred.Holds nodes facts source /\
  query.sinkPred.Holds nodes facts sink /\
  exists hops,
    cpgHopsPath edges hops source sink /\
    cpgHopsMatchFilters hops query.traversal.filters /\
    cpgHopNodePredicatesHold nodes facts hops query.hopDstPreds

def checkCPGNodeTraversal
    (nodes : List CPGNode) (facts : List CPGNodeFact) (edges : List CPGEdge)
    (query : CPGNodeQuery) (cert : CPGFindingCert) : Bool :=
  checkCPGTraversal nodes edges query.traversal cert &&
  checkCPGNodePredicate nodes facts cert.source query.sourcePred &&
  checkCPGNodePredicate nodes facts cert.sink query.sinkPred &&
  checkCPGHopNodePredicates nodes facts cert.hops query.hopDstPreds

theorem checked_cpg_node_traversal_match_sound
    {nodes : List CPGNode} {facts : List CPGNodeFact} {edges : List CPGEdge}
    {query : CPGNodeQuery} {cert : CPGFindingCert}
    (h : checkCPGNodeTraversal nodes facts edges query cert = true) :
    CPGNodeTraversalMatch nodes facts edges query cert.source cert.sink := by
  simp [checkCPGNodeTraversal, CPGNodeTraversalMatch] at h
  have htrav := checked_cpg_traversal_match_sound h.left.left.left
  have htravRaw := h.left.left.left
  simp [checkCPGTraversal] at htravRaw
  exact ⟨htrav,
    checkCPGNodePredicate_sound h.left.left.right,
    checkCPGNodePredicate_sound h.left.right,
    cert.hops,
    checkCPGHops_sound cert.hops cert.source cert.sink htravRaw.left.right,
    checkCPGHopsMatchFilters_sound cert.hops query.traversal.filters htravRaw.right,
    checkCPGHopNodePredicates_sound cert.hops query.hopDstPreds h.right⟩

theorem checked_cpg_node_traversal_finding_sound
    {nodes : List CPGNode} {facts : List CPGNodeFact} {edges : List CPGEdge}
    {query : CPGNodeQuery} {cert : CPGFindingCert}
    (h : checkCPGNodeTraversal nodes facts edges query cert = true) :
    CPGFinding edges query.traversal.sources query.traversal.sinks cert.source cert.sink := by
  simp [checkCPGNodeTraversal] at h
  exact checked_cpg_traversal_finding_sound h.left.left.left

/-! ## Demo: source call to sink call with node predicates -/

def sourceCallName : CPGName := 100
def sinkCallName : CPGName := 200
def userInputClass : SourceClass := 1
def commandSinkClass : SinkClass := 9

def cpgNodePredicateFacts : List CPGNodeFact :=
  [ CPGNodeFact.callName 10 sourceCallName
  , CPGNodeFact.sourceClass 10 userInputClass
  , CPGNodeFact.callName 13 sinkCallName
  , CPGNodeFact.sinkClass 13 commandSinkClass
  ]

def cpgNodePredicateQuery : CPGNodeQuery :=
  { traversal := cpgAstCfgDataQuery
  , sourcePred := CPGNodePredicate.sourceClassIs userInputClass
  , sinkPred := CPGNodePredicate.sinkClassIs commandSinkClass
  , hopDstPreds :=
      [ CPGNodePredicate.kindIs CPGNodeKind.expr
      , CPGNodePredicate.kindIs CPGNodeKind.stmt
      , CPGNodePredicate.callNameIs sinkCallName
      ]
  }

example :
    checkCPGNodeTraversal
      cpgTraversalNodes
      cpgNodePredicateFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgNodePredicateQuery
      cpgAstCfgDataCert = true := by
  native_decide

example :
    CPGNodeTraversalMatch
      cpgTraversalNodes
      cpgNodePredicateFacts
      (mergeComponentEdges cpgComponentGraph)
      cpgNodePredicateQuery
      10
      13 :=
  checked_cpg_node_traversal_match_sound
    (nodes := cpgTraversalNodes)
    (facts := cpgNodePredicateFacts)
    (cert := cpgAstCfgDataCert)
    (by native_decide)

example :
    CPGFinding
      (mergeComponentEdges cpgComponentGraph)
      cpgAstCfgDataQuery.sources
      cpgAstCfgDataQuery.sinks
      10
      13 :=
  checked_cpg_node_traversal_finding_sound
    (nodes := cpgTraversalNodes)
    (facts := cpgNodePredicateFacts)
    (edges := mergeComponentEdges cpgComponentGraph)
    (query := cpgNodePredicateQuery)
    (cert := cpgAstCfgDataCert)
    (by native_decide)

end PcSastLean
