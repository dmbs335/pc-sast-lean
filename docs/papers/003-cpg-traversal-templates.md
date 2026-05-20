# Iteration 003: CPG Traversal Templates

Paper thread:

- Continues Iteration 002 on Yamaguchi, Golde, Arp, and Rieck, "Modeling and
  Discovering Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- DOI/metadata: <https://doi.org/10.1109/SP.2014.44>

## Core Claim

The CPG paper does two things:

1. Merge AST, CFG, and dependence information into one graph.
2. Express vulnerability patterns as graph traversals over that graph.

Iteration 002 covered the first point with a component-edge merge theorem.  This
iteration covers a small version of the second point: a vulnerability template is
a source set, a sink set, and a sequence of edge-kind filters.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPG`: raw CPG path certificates.
- `PcSastLean.CPGConstruction`: component graph paths lift to merged CPG paths.
- `PcSastLean.CPGProvenance`: typed edge provenance obligations.

Gap before this iteration:

- A checked CPG path did not say which query pattern it satisfied.
- There was no semantics for vulnerability-template edge filters.
- The theory still treated CPG findings as source-to-sink paths, not as query
  traversal matches.

## Lean Patch

Added `PcSastLean.CPGTraversal`.

New artifacts:

- `CPGKindFilter`: edge-kind filters, including wildcard, exact kind, and
  one-of-many kind choices.
- `cpgHopsMatchFilters`: semantic relation between a concrete hop list and a
  filter sequence.
- `checkCPGHopsMatchFilters_sound`: accepted filter checks imply the semantic
  match relation.
- `CPGTraversalQuery`: source ids, sink ids, and edge-kind filters.
- `CPGTraversalMatch`: a query match means source/sink membership plus a real
  CPG hop path satisfying the filters.
- `checked_cpg_traversal_match_sound`: accepted traversal certificates imply
  `CPGTraversalMatch`.
- `checked_cpg_traversal_finding_sound`: accepted traversal certificates also
  imply ordinary `CPGFinding`.
- `checked_cpg_traversal_path_and_filters`: accepted traversal certificates
  produce both a `CPGPath` and a proof that the path kinds satisfy the template.

## What This Improves

The CPG layer now has a small end-to-end chain:

1. Component AST/CFG/PDG-style edges merge into CPG edges.
2. Component paths lift to ordinary CPG paths.
3. Traversal templates check source/sink sets and edge-kind constraints.
4. Accepted traversal certificates imply real CPG paths satisfying the template.

This is still tiny, but the shape is much closer to CPG/Joern/CodeQL-style SAST:
findings are no longer just arbitrary paths; they are paths accepted by a query
template.

## Remaining Gaps

- No node-property predicates, such as call name, operator kind, argument index,
  type, literal value, or sanitizer classification.
- No branching traversal combinators, joins, repetition, negation, or
  dominance/post-dominance predicates.
- No graph database semantics.
- No template precision or recall theorem.
- No proof that a real query compiler from Gremlin/CodeQL/Joern emits these
  filters soundly.

## Next Theorem Candidate

Add node predicates to traversal templates.  The most useful next slice is:

- source node must be a `call` with a checked source classification;
- sink node must be a `call` with a checked sink classification;
- intermediate node predicates can constrain argument position or call name.

That would connect CPG traversal templates back to source/sink policy rather
than only edge-kind shape.
