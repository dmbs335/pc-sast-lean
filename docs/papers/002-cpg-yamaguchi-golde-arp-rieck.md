# Iteration 002: Yamaguchi-Golde-Arp-Rieck Code Property Graphs

Paper:

- Fabian Yamaguchi, Nico Golde, Daniel Arp, Konrad Rieck, "Modeling and
  Discovering Vulnerabilities with Code Property Graphs", IEEE Symposium on
  Security and Privacy 2014, pp. 590-604.
- DOI/metadata: <https://doi.org/10.1109/SP.2014.44>
- PDF inspected: <https://www.ieee-security.org/TC/SP2014/papers/ModelingandDiscoveringVulnerabilitieswithCodePropertyGraphs.pdf>

## Core Claim

The paper introduces the Code Property Graph as a joint representation that
merges syntax, control flow, and dependence information.  Vulnerability
templates are then expressed as graph traversals over this combined property
graph.

## Mapping to This Repository

Already covered:

- `PcSastLean.CPG`: typed CPG nodes/edges, checked path certificates, and
  source-to-sink CPG finding soundness.
- `PcSastLean.CPGProvenance`: path-specific typed edge provenance and edge-kind
  sanity checks.
- `PcSastLean.IFDSCPGEmbedding`: accepted IFDS certificates can be encoded as
  CPG-style path certificates over an exploded-supergraph encoding.
- `PcSastLean.SourceBackedAdapters`: artifact-level CPG findings can be lifted
  into source-level CI findings only with source-location provenance.

Gap before this iteration:

- The repository treated the CPG as already built.
- It did not formalize the paper's merge step from AST, CFG, and PDG-style
  component graphs into one property graph.
- It did not prove that a path through component graph edges is preserved as a
  CPG path after merging.

## Lean Patch

Added `PcSastLean.CPGConstruction`.

New artifacts:

- `CPGComponentKind`: component edge kinds for AST, CFG, data dependence,
  control dependence, call, and return.
- `CPGComponentEdge.toCPGEdge`: lowers a component edge into a typed CPG edge.
- `mergeComponentEdges`: builds the merged CPG edge list from component edges.
- `component_edge_mem_merge`: every component edge appears in the merged CPG.
- `componentPath`: a path through component edges.
- `componentPath_to_CPGPath`: every valid component path lifts to a `CPGPath`
  over the merged graph.
- `cpg_component_path_cert_sound`: a component-path certificate implies ordinary
  CPG reachability after merging.
- `ComponentCPGEdgeCert` and `component_path_hops_have_provenance`: path-specific
  component provenance is preserved for each lifted CPG hop.

This moves the CPG layer one step closer to the original paper: CPG is now not
only a checked graph artifact, but also a verified merge target for smaller
component representations.

## Remaining Gaps

- No parser correctness proof.
- No full AST construction semantics.
- No dominance/post-dominance proof for control dependence.
- No alias-sensitive data dependence construction.
- No graph database or Gremlin traversal semantics.
- No vulnerability-template precision/recall theorem.
- No proof that Joern-style fuzzy parsing preserves all security-relevant
  program facts.

## Next Theorem Candidate

Add a query-template semantics layer: define a tiny graph traversal language with
edge-kind filters and prove that accepted traversal certificates correspond to
`CPGPath` facts.  This would address the paper's second half: vulnerabilities as
graph traversals, not merely graph paths.
