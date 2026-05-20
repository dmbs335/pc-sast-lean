import PcSastLean.CPGConstruction

/-!
CPG traversal templates.

The CPG paper's second key move is that vulnerability patterns are graph
traversals over the merged program representation.  `CPG.lean` checks a raw path;
`CPGConstruction.lean` checks that component graphs merge into CPG paths.  This
module adds a tiny query-template layer: a traversal template constrains a path
by source/sink sets and a sequence of edge-kind filters.

Claim boundary:

* Verified here: an accepted traversal certificate is a real CPG path and
  satisfies the template's edge-kind filters.
* External obligations: production query languages such as Gremlin/CodeQL/Joern
  traversals must be compiled into this certificate language soundly.
* Not modeled here: arbitrary graph predicates, joins, negation, aggregation,
  path quantifiers, ranking, query optimization, or precision/recall.
-/

namespace PcSastLean

inductive CPGKindFilter where
  | any
  | one (kind : CPGEdgeKind)
  | oneOf (kinds : List CPGEdgeKind)
deriving DecidableEq, Repr

def CPGKindFilter.Accepts : CPGKindFilter -> CPGEdgeKind -> Prop
  | CPGKindFilter.any, _ => True
  | CPGKindFilter.one expected, actual => actual = expected
  | CPGKindFilter.oneOf expected, actual => actual ∈ expected

def checkCPGKindFilter (filter : CPGKindFilter) (kind : CPGEdgeKind) : Bool :=
  match filter with
  | CPGKindFilter.any => true
  | CPGKindFilter.one expected => decide (kind = expected)
  | CPGKindFilter.oneOf expected => decide (kind ∈ expected)

def cpgHopsMatchFilters : List CPGHop -> List CPGKindFilter -> Prop
  | [], [] => True
  | hop :: restHops, filter :: restFilters =>
      filter.Accepts hop.kind /\ cpgHopsMatchFilters restHops restFilters
  | _, _ => False

def checkCPGHopsMatchFilters : List CPGHop -> List CPGKindFilter -> Bool
  | [], [] => true
  | hop :: restHops, filter :: restFilters =>
      checkCPGKindFilter filter hop.kind &&
      checkCPGHopsMatchFilters restHops restFilters
  | _, _ => false

theorem checkCPGKindFilter_sound
    {filter : CPGKindFilter} {kind : CPGEdgeKind}
    (h : checkCPGKindFilter filter kind = true) :
    filter.Accepts kind := by
  cases filter with
  | any =>
      trivial
  | one expected =>
      simp [checkCPGKindFilter, CPGKindFilter.Accepts] at h
      exact h
  | oneOf expected =>
      simp [checkCPGKindFilter, CPGKindFilter.Accepts] at h
      exact h

theorem checkCPGHopsMatchFilters_sound :
    forall hops filters,
      checkCPGHopsMatchFilters hops filters = true ->
      cpgHopsMatchFilters hops filters := by
  intro hops
  induction hops with
  | nil =>
      intro filters h
      cases filters with
      | nil =>
          trivial
      | cons _ _ =>
          simp [checkCPGHopsMatchFilters] at h
  | cons hop rest ih =>
      intro filters h
      cases filters with
      | nil =>
          simp [checkCPGHopsMatchFilters] at h
      | cons filter restFilters =>
          simp [checkCPGHopsMatchFilters, cpgHopsMatchFilters] at h ⊢
          exact ⟨checkCPGKindFilter_sound h.left, ih restFilters h.right⟩

def cpgKindsMatchFilters : List CPGEdgeKind -> List CPGKindFilter -> Prop
  | [], [] => True
  | kind :: restKinds, filter :: restFilters =>
      filter.Accepts kind /\ cpgKindsMatchFilters restKinds restFilters
  | _, _ => False

theorem cpg_hops_match_filters_to_kinds
    {hops : List CPGHop} {filters : List CPGKindFilter}
    (h : cpgHopsMatchFilters hops filters) :
    cpgKindsMatchFilters (cpgHopKinds hops) filters := by
  induction hops generalizing filters with
  | nil =>
      cases filters with
      | nil =>
          trivial
      | cons _ _ =>
          cases h
  | cons hop rest ih =>
      cases filters with
      | nil =>
          cases h
      | cons filter restFilters =>
          rcases h with ⟨hhead, htail⟩
          simp [cpgHopKinds, cpgKindsMatchFilters]
          exact ⟨hhead, ih htail⟩

structure CPGTraversalQuery where
  sources : List CPGId
  sinks : List CPGId
  filters : List CPGKindFilter
deriving Repr

def CPGTraversalMatch
    (edges : List CPGEdge) (query : CPGTraversalQuery)
    (source sink : CPGId) : Prop :=
  source ∈ query.sources /\
  sink ∈ query.sinks /\
  exists hops,
    cpgHopsPath edges hops source sink /\
    cpgHopsMatchFilters hops query.filters

def checkCPGTraversal
    (nodes : List CPGNode) (edges : List CPGEdge)
    (query : CPGTraversalQuery) (cert : CPGFindingCert) : Bool :=
  checkHasNode nodes cert.source &&
  checkHasNode nodes cert.sink &&
  decide (cert.source ∈ query.sources) &&
  decide (cert.sink ∈ query.sinks) &&
  checkCPGHops edges cert.hops cert.source cert.sink &&
  checkCPGHopsMatchFilters cert.hops query.filters

theorem checked_cpg_traversal_match_sound
    {nodes : List CPGNode} {edges : List CPGEdge}
    {query : CPGTraversalQuery} {cert : CPGFindingCert}
    (h : checkCPGTraversal nodes edges query cert = true) :
    CPGTraversalMatch edges query cert.source cert.sink := by
  simp [checkCPGTraversal, CPGTraversalMatch] at h
  exact ⟨h.left.left.left.right, h.left.left.right,
    cert.hops,
    checkCPGHops_sound cert.hops cert.source cert.sink h.left.right,
    checkCPGHopsMatchFilters_sound cert.hops query.filters h.right⟩

theorem checked_cpg_traversal_finding_sound
    {nodes : List CPGNode} {edges : List CPGEdge}
    {query : CPGTraversalQuery} {cert : CPGFindingCert}
    (h : checkCPGTraversal nodes edges query cert = true) :
    CPGFinding edges query.sources query.sinks cert.source cert.sink := by
  have hmatch := checked_cpg_traversal_match_sound h
  rcases hmatch with ⟨hsource, hsink, hops, hpath, _hfilters⟩
  exact ⟨hsource, hsink, cpgHopKinds hops, cpgHopsPath_to_CPGPath hops cert.source cert.sink hpath⟩

theorem checked_cpg_traversal_path_and_filters
    {nodes : List CPGNode} {edges : List CPGEdge}
    {query : CPGTraversalQuery} {cert : CPGFindingCert}
    (h : checkCPGTraversal nodes edges query cert = true) :
    exists kinds,
      CPGPath edges cert.source cert.sink kinds /\
      cpgKindsMatchFilters kinds query.filters := by
  have hmatch := checked_cpg_traversal_match_sound h
  rcases hmatch with ⟨_hsource, _hsink, hops, hpath, hfilters⟩
  exact ⟨cpgHopKinds hops,
    cpgHopsPath_to_CPGPath hops cert.source cert.sink hpath,
    cpg_hops_match_filters_to_kinds hfilters⟩

/-! ## Demo: a vulnerability template over merged CPG components -/

def cpgTraversalNodes : List CPGNode :=
  [ { id := 10, kind := CPGNodeKind.call, loc := demoLoc }
  , { id := 11, kind := CPGNodeKind.expr, loc := demoLoc }
  , { id := 12, kind := CPGNodeKind.stmt, loc := demoLoc }
  , { id := 13, kind := CPGNodeKind.call, loc := demoLoc }
  ]

def cpgAstCfgDataQuery : CPGTraversalQuery :=
  { sources := [10]
  , sinks := [13]
  , filters :=
      [ CPGKindFilter.one CPGEdgeKind.ast
      , CPGKindFilter.one CPGEdgeKind.cfg
      , CPGKindFilter.one CPGEdgeKind.data
      ]
  }

def cpgAstCfgDataCert : CPGFindingCert :=
  { source := 10
  , sink := 13
  , hops :=
      [ cpgAstComponent.toHop
      , cpgCfgComponent.toHop
      , cpgDataComponent.toHop
      ]
  }

example :
    checkCPGTraversal
      cpgTraversalNodes
      (mergeComponentEdges cpgComponentGraph)
      cpgAstCfgDataQuery
      cpgAstCfgDataCert = true := by
  native_decide

example :
    CPGTraversalMatch
      (mergeComponentEdges cpgComponentGraph)
      cpgAstCfgDataQuery
      10
      13 :=
  checked_cpg_traversal_match_sound
    (nodes := cpgTraversalNodes)
    (cert := cpgAstCfgDataCert)
    (by native_decide)

example :
    exists kinds,
      CPGPath (mergeComponentEdges cpgComponentGraph) 10 13 kinds /\
      cpgKindsMatchFilters kinds cpgAstCfgDataQuery.filters :=
  checked_cpg_traversal_path_and_filters
    (nodes := cpgTraversalNodes)
    (cert := cpgAstCfgDataCert)
    (by native_decide)

end PcSastLean
