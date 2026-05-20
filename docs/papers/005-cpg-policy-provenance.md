# Iteration 005: CPG Source/Sink Policy Provenance

Paper thread:

- Continues the CPG line from Yamaguchi, Golde, Arp, and Rieck, "Modeling and
  Discovering Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- DOI/metadata: <https://doi.org/10.1109/SP.2014.44>

## Core Claim

CPG vulnerability templates ultimately depend on security policy: which calls are
sources, which calls are sinks, and which classes of source/sink they represent.

Iteration 004 allowed node predicates to require source and sink class facts.
This iteration adds policy provenance for those facts.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPGNodePredicates`: traversal matches can require checked node
  facts such as call names and source/sink classes.
- `PcSastLean.CPGTraversal`: traversal templates check edge-kind path shape.
- `PcSastLean.CPGConstruction`: component graph paths lift into merged CPG paths.

Gap before this iteration:

- `sourceClass` and `sinkClass` facts were opaque metadata.
- There was no checked link from classification facts to source/sink policy
  rules.
- A CPG node-predicate finding could satisfy a class predicate without showing
  why the endpoint node deserved that class.

## Lean Patch

Added `PcSastLean.CPGPolicyProvenance`.

New artifacts:

- `CPGPolicyRule`: source and sink policy rules keyed by checked call-name ids
  and source/sink classes.
- `CPGPolicyFactCert`: a certificate that a specific node has a source or sink
  class because a call-name fact and a policy rule agree.
- `checkCPGPolicyFactCert_sound`: accepted policy fact certificates imply the
  trusted policy-backed fact semantics.
- `SourcePolicyMatches` and `SinkPolicyMatches`: endpoint policy certificates
  must match the finding source/sink and the query's expected source/sink
  predicates.
- `CPGPolicyBackedTraversalCert`: a CPG finding certificate plus endpoint policy
  certificates.
- `CPGPolicyBackedTraversalMatch`: a node-predicate traversal match with
  source/sink facts backed by policy rules.
- `checked_cpg_policy_backed_traversal_sound`: accepted policy-backed traversal
  certificates imply `CPGPolicyBackedTraversalMatch`.
- `checked_cpg_policy_backed_finding_sound`: accepted policy-backed traversal
  certificates still imply ordinary `CPGFinding`.

## What This Improves

The CPG query chain now has a clearer trust boundary:

1. Component edges merge into CPG edges.
2. Traversal filters constrain path shape.
3. Node predicates constrain endpoint/intermediate properties.
4. Source/sink endpoint classifications are backed by explicit policy rules.

That moves source/sink classification from "metadata we hope is right" to a
checked artifact: the node has a call-name fact, the policy contains a matching
source/sink rule, and the query expects that class.

## Remaining Gaps

- Call names are still numeric ids, not real strings.
- Call-name extraction is still trusted metadata.
- Policy rules are assumed present; there is no DSL or proof that a real policy
  file compiled into them correctly.
- No sanitizer policy provenance yet.
- No framework-specific source/sink discovery, type signatures, receiver
  dispatch, or overload handling.

## Next Theorem Candidate

Add sanitizer policy provenance for CPG traversal queries:

- a sanitizer node fact should be backed by a sanitizer policy rule;
- a traversal finding should be suppressible only when a sanitizer predicate
  proves the required source-to-sink class is neutralized;
- the result should connect CPG node predicates with the existing
  `SanitizerLattice`.
