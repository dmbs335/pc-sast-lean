# Iteration 011: CPG No-Orphan Adapters

Paper thread:

- Continues Yamaguchi, Golde, Arp, and Rieck, "Modeling and Discovering
  Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- Primary paper PDF: <https://www.ieee-security.org/TC/SP2014/papers/ModelingandDiscoveringVulnerabilitieswithCodePropertyGraphs.pdf>
- Joern CPG specification: <https://cpg.joern.io/>

## Core Claim

Iteration 010 added extraction-origin certificates for CPG hops.  This
iteration makes that evidence operational: the CPG adapters that feed analyzer
runs and sanitizer triage can require every finding-path hop to have checked
origin provenance.

The result is a no-orphan-edge adapter discipline:

> A CPG finding may enter the top-level analyzer/triage layer only through a
> checker that accepts both the vulnerability evidence and extraction-origin
> coverage for every hop.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPGExtractionProvenance`: checks per-hop AST/CFG/DDG/CDG/call/return
  extraction origins.
- `PcSastLean.CPGTraversal`: checks CPG finding paths and traversal templates.
- `PcSastLean.CPGSanitizerTriage`: turns ordered sanitizer evidence into
  proof-carrying triage evidence.

Gap before this iteration:

- Extraction-origin checking existed as a separate theorem.
- Ordinary analyzer runs and sanitizer triage evidence could still be built
  from the older CPG checker interface.
- The theory had not yet stated that an operational CPG adapter can refuse
  orphan hops.

## Lean Patch

Added `PcSastLean.CPGNoOrphanAdapter`.

New artifacts:

- `CPGNoOrphanFindingCert`: CPG finding certificate plus extraction-origin
  certificates.
- `checkCPGNoOrphanFinding`: combines `checkCPGFinding` with
  `checkExtractedHops`.
- `CPGNoOrphanFindingMatch`: trusted proposition containing both the CPG finding
  and per-hop origin coverage.
- `checked_cpg_no_orphan_finding_sound`: accepted no-orphan finding evidence
  implies `CPGNoOrphanFindingMatch`.
- `cpgNoOrphanFindingRun`: analyzer run produced from no-orphan evidence.
- `cpgNoOrphanFindingRun_sound`: the run satisfies `AnalyzerRun.Sound`.
- `cpgNoOrphanFindingRun_hops_have_origins`: every hop used by the run has a
  typed extraction origin.
- `CPGNoOrphanOrderedSanitizerCert`: ordered sanitizer certificate plus
  extraction-origin certificates for the underlying finding path.
- `checkCPGNoOrphanOrderedSanitizer`: combines ordered sanitizer checking with
  hop-origin checking.
- `checked_cpg_no_orphan_ordered_sanitizer_sound`: accepted evidence yields
  ordered sanitizer semantics and per-hop origin coverage.
- `cpgNoOrphanOrderedSanitizerRun_sound`: sanitizer-triage analyzer runs remain
  sound under the no-orphan adapter.
- `noOrphanOrderedSanitizerTriageEvidence_sound`: proof-carrying sanitizer
  triage evidence still works after provenance is required.

## What This Improves

This closes a practical integration gap.  Previously, provenance could be
checked, but it was not on the main route into analyzer/triage runs.  Now the
route can be:

1. Check CPG finding or ordered sanitizer evidence.
2. Check extraction-origin coverage for every hop in the finding path.
3. Only then produce an analyzer run or sanitizer triage evidence.

The result is not full source-level soundness, but it is a stronger artifact
contract.  A top-level CPG result cannot be built through this adapter from a
path that contains an unexplained edge.

## Remaining Gaps

- Source-backed adapters do not yet consume no-orphan CPG runs.
- Real extraction algorithms still need proofs that their origin facts are
  correct.
- The adapter does not prove extraction completeness or analyzer recall.
- Value-flow tokens and DDG origins are still toy-level abstractions.
- Query-language compilation from production CPG queries remains external.

## Next Theorem Candidate

Lift source-backed adapters through no-orphan CPG adapters:

- tie source-level sink provenance to a no-orphan CPG finding run;
- prove source-level reports inherit both artifact-sink soundness and per-hop
  extraction-origin coverage.
