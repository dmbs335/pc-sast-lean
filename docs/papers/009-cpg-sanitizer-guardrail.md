# Iteration 009: CPG Wrong-Context Sanitizer Guardrail

Paper thread:

- Continues the CPG line from Yamaguchi, Golde, Arp, and Rieck, "Modeling and
  Discovering Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- Primary paper PDF: <https://www.ieee-security.org/TC/SP2014/papers/ModelingandDiscoveringVulnerabilitieswithCodePropertyGraphs.pdf>
- DOI/metadata: <https://doi.org/10.1109/SP.2014.44>

## Core Claim

CPG traversals are useful because they let vulnerability templates combine
syntax, control flow, and dependence information.  But once sanitizer evidence
is allowed to suppress a finding, the checker needs a negative guarantee:
"some sanitizer" is not enough.  The sanitizer capability must match the sink
context.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPGSanitizerPolicy`: sanitizer call-name policy and sink-class
  requirements connect to `SanitizerLattice`.
- `PcSastLean.CPGOrderedSanitizer`: sanitizer evidence must precede the sink and
  carry the same value token.
- `PcSastLean.CPGSanitizerTriage`: ordered sanitizer evidence can become
  proof-carrying triage evidence.

Gap before this iteration:

- The positive path was documented, but the negative guardrail was not explicit.
- A reviewer had to inspect the checker composition to see that a SQL sanitizer
  could not suppress a shell sink.
- The CPG layer did not have a theorem analogous to
  `wrong_context_sanitizer_does_not_prove_html_safe`.

## Lean Patch

Added `PcSastLean.CPGSanitizerGuardrail`.

New artifacts:

- `sanitizerCertKind`: extracts the `SinkKind` claimed by a sanitizer
  certificate.
- `wrong_context_sanitizer_does_not_prove_safe`: generic sanitizer-lattice
  negative theorem for unequal sink kinds.
- `checked_sanitizer_kind_matches_required`: any accepted sanitizer-backed CPG
  traversal forces sanitizer kind equality with the sink requirement.
- `wrong_context_sanitized_traversal_rejected`: wrong-context sanitizer-backed
  traversal certificates cannot pass the checker.
- `checked_ordered_sanitizer_kind_matches_required`: the same equality result
  for ordered value-flow sanitizer evidence.
- `wrong_context_ordered_sanitizer_rejected`: wrong-context ordered sanitizer
  evidence cannot pass and therefore cannot become proof-carrying triage
  evidence.
- Demo certificate: a SQL sanitizer on the path to a shell sink is rejected even
  when the sanitizer node, ordering, and value token facts are otherwise present.

## What This Improves

This iteration turns an implicit safety property into a named theorem:

1. Positive evidence still works when sanitizer kind and sink requirement match.
2. Wrong-context evidence is rejected at the checker level.
3. Rejection holds for both sanitizer-backed traversals and ordered value-flow
   sanitizer traversals.
4. Because triage evidence requires accepted ordered sanitizer evidence,
   wrong-context sanitizer evidence cannot suppress the modeled CPG finding.

This is not merely a boolean unfolding result at the CI layer.  It pins the
context-indexed sanitizer lattice to the graph certificate layer and proves the
negative case that reviewers actually worry about.

## Remaining Gaps

- Correct extraction of sanitizer call names and sink-class requirements remains
  a CPG provenance obligation.
- Value-flow tokens are still toy facts; alias-sensitive token computation is
  not verified.
- Parser-state sanitizers and composed sanitizer chains are not modeled.
- The concrete semantics used for CPG sanitizer triage is still deliberately
  narrow.

## Next Theorem Candidate

Move from sanitizer-context guardrails to CPG extraction provenance:

- represent AST/CFG/DDG/CDG extraction rules as certificate-producing steps;
- prove that each typed CPG edge has a source-level justification;
- use that to reduce the current `cpgExtractionProvenance` obligation.
