import PcSastLean.CPGProvenance

/-!
CPG construction from component graphs.

Yamaguchi et al.'s Code Property Graph idea is not merely "a graph with typed
edges"; it is a merge of classic program representations: AST, CFG, and program
dependence graph edges.  `CPG.lean` checks paths after such a graph exists.
This module adds a small construction layer: component edges lower to CPG edges,
and paths through component edges lift to ordinary CPG paths over the merged
graph.

Claim boundary:

* Verified here: component AST/CFG/PDG/call/return edges become typed CPG edges,
  and component paths are preserved by the merge.
* External obligations: production builders must prove that their component
  AST, CFG, DDG, CDG, call, and return edges are correct for the source program.
* Not modeled here: parser correctness, full C/C++ AST semantics, dominance-
  based control dependence construction, alias-sensitive data dependence, graph
  database query semantics, or vulnerability-template precision.
-/

namespace PcSastLean

inductive CPGComponentKind where
  | ast
  | cfg
  | data
  | control
  | call
  | ret
deriving DecidableEq, Repr

def CPGComponentKind.toEdgeKind : CPGComponentKind -> CPGEdgeKind
  | CPGComponentKind.ast => CPGEdgeKind.ast
  | CPGComponentKind.cfg => CPGEdgeKind.cfg
  | CPGComponentKind.data => CPGEdgeKind.data
  | CPGComponentKind.control => CPGEdgeKind.control
  | CPGComponentKind.call => CPGEdgeKind.call
  | CPGComponentKind.ret => CPGEdgeKind.ret

structure CPGComponentEdge where
  src : CPGId
  dst : CPGId
  kind : CPGComponentKind
  loc : SourceLoc
deriving DecidableEq, Repr

def CPGComponentEdge.toCPGEdge (edge : CPGComponentEdge) : CPGEdge :=
  { src := edge.src
  , dst := edge.dst
  , kind := edge.kind.toEdgeKind
  , loc := edge.loc
  }

def CPGComponentEdge.toHop (edge : CPGComponentEdge) : CPGHop :=
  { src := edge.src
  , dst := edge.dst
  , kind := edge.kind.toEdgeKind
  , loc := edge.loc
  }

def mergeComponentEdges (edges : List CPGComponentEdge) : List CPGEdge :=
  edges.map (fun e => e.toCPGEdge)

theorem component_edge_mem_merge
    {components : List CPGComponentEdge} {edge : CPGComponentEdge}
    (h : edge ∈ components) :
    edge.toCPGEdge ∈ mergeComponentEdges components := by
  unfold mergeComponentEdges
  exact List.mem_map.mpr ⟨edge, h, rfl⟩

theorem component_edge_kind_sound
    (edge : CPGComponentEdge) :
    edge.toCPGEdge.kind = edge.kind.toEdgeKind := by
  rfl

def componentPath
    (components : List CPGComponentEdge) :
    List CPGComponentEdge -> CPGId -> CPGId -> Prop
  | [], src, dst => src = dst
  | edge :: rest, src, dst =>
      edge ∈ components /\
      edge.src = src /\
      componentPath components rest edge.dst dst

def componentPathKinds : List CPGComponentEdge -> List CPGEdgeKind
  | [] => []
  | edge :: rest => edge.kind.toEdgeKind :: componentPathKinds rest

theorem componentPath_to_CPGPath
    {components : List CPGComponentEdge} :
    forall path src dst,
      componentPath components path src dst ->
      CPGPath (mergeComponentEdges components) src dst (componentPathKinds path) := by
  intro path
  induction path with
  | nil =>
      intro src dst h
      simp [componentPath] at h
      subst h
      exact CPGPath.refl src
  | cons edge rest ih =>
      intro src dst h
      rcases h with ⟨hedge, hsrc, hrest⟩
      subst hsrc
      simp [componentPathKinds]
      exact CPGPath.cons
        (component_edge_mem_merge (components := components) hedge)
        (ih edge.dst dst hrest)

structure CPGComponentPathCert where
  source : CPGId
  sink : CPGId
  path : List CPGComponentEdge
deriving Repr

def CPGComponentPathCert.Valid
    (components : List CPGComponentEdge) (cert : CPGComponentPathCert) : Prop :=
  componentPath components cert.path cert.source cert.sink

theorem cpg_component_path_cert_sound
    {components : List CPGComponentEdge} {cert : CPGComponentPathCert}
    (h : cert.Valid components) :
    exists kinds,
      CPGPath (mergeComponentEdges components) cert.source cert.sink kinds := by
  exact ⟨componentPathKinds cert.path,
    componentPath_to_CPGPath cert.path cert.source cert.sink h⟩

/-! ## Path-specific component provenance -/

structure ComponentCPGEdgeCert where
  component : CPGComponentEdge
  edge : CPGEdge
deriving Repr

def ComponentCPGEdgeCert.Sound (cert : ComponentCPGEdgeCert) : Prop :=
  cert.edge = cert.component.toCPGEdge

def componentCerts (components : List CPGComponentEdge) : List ComponentCPGEdgeCert :=
  components.map (fun c => { component := c, edge := c.toCPGEdge })

def ComponentHopCertified
    (certs : List ComponentCPGEdgeCert) (hop : CPGHop) : Prop :=
  exists cert,
    cert ∈ certs /\
    cert.edge = hop.edge /\
    cert.Sound

theorem component_hop_certified
    {components : List CPGComponentEdge} {edge : CPGComponentEdge}
    (h : edge ∈ components) :
    ComponentHopCertified (componentCerts components) edge.toHop := by
  refine ⟨{ component := edge, edge := edge.toCPGEdge }, ?_, ?_, rfl⟩
  · unfold componentCerts
    exact List.mem_map.mpr ⟨edge, h, rfl⟩
  · simp [CPGComponentEdge.toHop, CPGHop.edge, CPGComponentEdge.toCPGEdge]

theorem component_path_hops_have_provenance
    {components path : List CPGComponentEdge} {src dst : CPGId}
    (hpath : componentPath components path src dst) :
    forall edge, edge ∈ path ->
      ComponentHopCertified (componentCerts components) edge.toHop := by
  intro edge hedge
  induction path generalizing src with
  | nil =>
      simp at hedge
  | cons head rest ih =>
      rcases hpath with ⟨hhead, _hsrc, hrest⟩
      simp at hedge
      cases hedge with
      | inl heq =>
          subst heq
          exact component_hop_certified hhead
      | inr htail =>
          exact ih hrest htail

/-! ## Demo: AST plus CFG plus data dependence in one CPG -/

def cpgAstComponent : CPGComponentEdge :=
  { src := 10, dst := 11, kind := CPGComponentKind.ast, loc := demoLoc }

def cpgCfgComponent : CPGComponentEdge :=
  { src := 11, dst := 12, kind := CPGComponentKind.cfg, loc := demoLoc }

def cpgDataComponent : CPGComponentEdge :=
  { src := 12, dst := 13, kind := CPGComponentKind.data, loc := demoLoc }

def cpgComponentGraph : List CPGComponentEdge :=
  [cpgAstComponent, cpgCfgComponent, cpgDataComponent]

def cpgComponentCert : CPGComponentPathCert :=
  { source := 10
  , sink := 13
  , path := [cpgAstComponent, cpgCfgComponent, cpgDataComponent]
  }

theorem cpgComponentCertValid :
    cpgComponentCert.Valid cpgComponentGraph := by
  simp [CPGComponentPathCert.Valid, cpgComponentCert, cpgComponentGraph,
    componentPath, cpgAstComponent, cpgCfgComponent, cpgDataComponent]

example :
    exists kinds,
      CPGPath (mergeComponentEdges cpgComponentGraph) 10 13 kinds :=
  cpg_component_path_cert_sound cpgComponentCertValid

example :
    componentPathKinds cpgComponentCert.path =
      [CPGEdgeKind.ast, CPGEdgeKind.cfg, CPGEdgeKind.data] := by
  rfl

example :
    forall edge, edge ∈ cpgComponentCert.path ->
      ComponentHopCertified (componentCerts cpgComponentGraph) edge.toHop :=
  component_path_hops_have_provenance cpgComponentCertValid

end PcSastLean
