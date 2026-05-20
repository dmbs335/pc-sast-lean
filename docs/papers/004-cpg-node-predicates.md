# Iteration 004: CPG Node Predicates

Paper thread:

- Continues the CPG line from Yamaguchi, Golde, Arp, and Rieck, "Modeling and
  Discovering Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- DOI/metadata: <https://doi.org/10.1109/SP.2014.44>

## Core Claim

Real CPG vulnerability templates do not match paths only by edge shape.  They
also inspect node properties: call names, source/sink classifications, argument
positions, types, and other property-graph attributes.

Iteration 003 added edge-kind traversal filters.  This iteration adds checked
node facts and node predicates.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPGTraversal`: source/sink sets plus edge-kind filters define a
  tiny traversal template.
- `PcSastLean.CPGConstruction`: component graph paths lift into merged CPG paths.
- `PcSastLean.CPGProvenance`: typed edge provenance obligations.

Gap before this iteration:

- Traversal templates could not require the source node to be a source call.
- Traversal templates could not require the sink node to be a sink call.
- Intermediate path nodes could not be constrained by kind, call name, or
  argument position.

## Lean Patch

Added `PcSastLean.CPGNodePredicates`.

New artifacts:

- `CPGNodeFact`: external property facts for call names, argument indices,
  source classes, and sink classes.
- `CPGNodePredicate`: query predicates over node kind and checked node facts.
- `checkCPGNodePredicate_sound`: accepted node-predicate checks imply the trusted
  predicate semantics.
- `cpgHopNodePredicatesHold`: semantic relation between path-hop destination
  nodes and predicate sequences.
- `checkCPGHopNodePredicates_sound`: accepted hop-node predicate checks imply
  the semantic relation.
- `CPGNodeQuery`: traversal template plus source, sink, and hop destination node
  predicates.
- `CPGNodeTraversalMatch`: a traversal match with both edge-kind filters and
  checked node predicates.
- `checked_cpg_node_traversal_match_sound`: accepted node-predicate traversal
  certificates imply `CPGNodeTraversalMatch`.
- `checked_cpg_node_traversal_finding_sound`: accepted node-predicate traversal
  certificates still imply ordinary `CPGFinding`.

## What This Improves

The CPG query slice now checks both:

- path shape: source/sink sets plus edge-kind filters;
- node properties: source class, sink class, call name, node kind, and argument
  index facts.

This is closer to practical Joern/CodeQL-style SAST queries, where a finding is
not just "some path" but a path whose endpoints and intermediate nodes satisfy a
security-relevant query template.

## Remaining Gaps

- Node facts are still uninterpreted metadata.  A production CPG builder must
  prove that call names, argument indices, and source/sink classifications are
  extracted correctly.
- No string values, type hierarchy, overload resolution, receiver dispatch, or
  variadic argument semantics.
- No path repetition, branching, joins, negation, aggregation, or dataflow query
  recursion.
- No precision/recall theorem for vulnerability templates.

## Next Theorem Candidate

Add source/sink policy provenance:

- a checked source-class fact should be backed by a source policy rule;
- a checked sink-class fact should be backed by a sink policy rule;
- node-predicate traversal findings should lift into CI reports only when those
  policy facts are present.

That would connect CPG traversal templates to the security policy boundary,
rather than treating source/sink classes as opaque metadata.
