# Iteration 007: Ordered and Value-Carrying CPG Sanitizer Evidence

Paper thread:

- Continues the CPG line from Yamaguchi, Golde, Arp, and Rieck, "Modeling and
  Discovering Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- DOI/metadata: <https://doi.org/10.1109/SP.2014.44>

## Core Claim

Sanitizer evidence is only useful when the sanitizer is actually on the relevant
source-to-sink value flow.  Merely showing that a sanitizer node appears
somewhere on a path is too weak.

Iteration 006 connected CPG sanitizer facts to the sanitizer lattice, but its
coverage relation only required membership in the path.  This iteration adds
ordered and value-carrying evidence.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPGSanitizerPolicy`: sanitizer policy facts connect to
  `SanitizerLattice`.
- `PcSastLean.CPGPolicyProvenance`: source/sink endpoints are policy-backed.
- `PcSastLean.CPGTraversal`: CPG paths satisfy traversal templates.

Gap before this iteration:

- Sanitizer coverage did not require sanitizer-before-sink ordering.
- Sanitizer coverage did not require the sanitizer output and sink input to be
  the same value.
- The sanitizer evidence was therefore too close to "a sanitizer exists nearby".

## Lean Patch

Added `PcSastLean.CPGOrderedSanitizer`.

New artifacts:

- `FlowToken`: a toy value-identity token.
- `CPGValueFlowFact`: sanitizer-output and sink-input facts tagged with a
  `FlowToken`.
- `BeforeInList` and `checkBeforeInList_sound`: checked ordering over hop
  destination lists.
- `OrderedSanitizerCoversFinding`: the sanitizer node occurs before the sink and
  provides the required `SinkKind`.
- `ValueTokenCarriesSanitizedFlow`: the sanitizer output and sink input share a
  checked flow token.
- `CPGOrderedSanitizedTraversalCert`: sanitizer-backed traversal plus a flow
  token.
- `CPGOrderedSanitizedTraversalMatch`: sanitizer-backed traversal with ordering
  and value-token evidence.
- `checked_cpg_ordered_sanitized_traversal_sound`: accepted ordered sanitizer
  certificates imply `CPGOrderedSanitizedTraversalMatch`.
- `checked_cpg_ordered_sanitized_finding_sound`: accepted ordered sanitizer
  certificates still imply ordinary `CPGFinding`.

## What This Improves

Sanitizer evidence now has three pieces:

1. policy: the sanitizer call provides the sink's required `SinkKind`;
2. order: the sanitizer node occurs before the sink node on the path;
3. value identity: the sanitizer output token is the sink input token.

This is still a toy token model, but it is substantially closer to what practical
SAST must prove before using sanitizer evidence to discharge a finding.

## Remaining Gaps

- Flow tokens are trusted metadata; there is no proof that they are computed
  correctly from real data dependence.
- Ordering is over hop destination lists, not a full path/dominance semantics.
- No branch/path feasibility interaction.
- No alias-sensitive value identity.
- No suppression theorem yet that uses ordered sanitizer evidence to remove a CPG
  false positive from CI triage.

## Next Theorem Candidate

Use ordered sanitizer evidence as proof-carrying triage evidence:

- if a CPG finding has ordered sanitizer evidence for the sink's required
  context, it can be suppressed as not a concrete vulnerability for that modeled
  policy;
- the proof should feed into `TriageEvidence` and the CI no-bug-hiding theorem.
