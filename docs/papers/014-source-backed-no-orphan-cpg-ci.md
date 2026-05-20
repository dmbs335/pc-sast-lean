# Iteration 014: CI Gate for Source-Backed No-Orphan CPG Batches

Paper thread:

- Continues Yamaguchi, Golde, Arp, and Rieck, "Modeling and Discovering
  Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- Primary paper PDF: <https://www.ieee-security.org/TC/SP2014/papers/ModelingandDiscoveringVulnerabilitieswithCodePropertyGraphs.pdf>
- Joern CPG specification: <https://cpg.joern.io/>

## Core Claim

Iteration 013 proved that multi-finding source-backed no-orphan CPG batches are
sound and preserve hop-origin evidence.  This iteration connects that batch run
to the top-level CI no-bug-hiding gate.

The new end-to-end shape is:

1. Check every no-orphan CPG entry.
2. Check source/artifact provenance obligations.
3. Build a source-level batch analyzer run.
4. Use the checked abstract source report as the CI report.
5. Prove no modeled concrete source bug is hidden.
6. Retain the theorem that every underlying CPG hop has an extraction origin.

## Lean Patch

Added `PcSastLean.SourceBackedNoOrphanCPGCI`.

New artifacts:

- `sourceBackedNoOrphanCPGBatchTriage`: a `TriageRun` whose report is the
  source-level batch abstract report.
- `sourceBackedNoOrphanCPGBatchTriage_complete`: the report is complete for the
  batch run.
- `sourceBackedNoOrphanCPGBatch_ci_no_bug_hiding`: checked no-orphan entries
  plus source/artifact provenance imply every concrete modeled source bug is in
  the CI report.
- `sourceBackedNoOrphanCPGBatch_ci_not_reported_not_concrete`: absence from the
  CI report implies absence from the modeled concrete source CPG batch.
- `sourceBackedNoOrphanCPGBatch_ci_hops_have_origins`: every checked CPG entry
  still has per-hop extraction-origin coverage at the CI layer.
- `sourceBackedNoOrphanCPGBatch_ci_report_and_origins`: packages report
  no-bug-hiding and hop-origin preservation together.

## What This Improves

The source-backed no-orphan CPG story now reaches the top-level CI theorem:

- source findings are tied to artifact sinks;
- artifact CPG paths are no-orphan paths;
- the aggregate source run is sound;
- complete triage cannot hide a modeled concrete source bug;
- the audit trail for each CPG hop remains available.

This is the strongest CPG integration path in the repository so far.

## Remaining Gaps

- Source/artifact provenance soundness and extraction-origin correctness remain
  external obligations.
- The CI report here is the full abstract report; proof-carrying suppressions
  for source-backed no-orphan CPG batches are future work.
- Real CPG extraction algorithms are not verified.
- Query-language compilation from production CPG queries remains external.

## Next Theorem Candidate

Return to one of the broader gaps now that the CPG adapter chain is closed:

- object-sensitive keys with real call strings / receiver-type sensitivity; or
- byte-range pointer-disjoint suppression; or
- richer SMT proof certificates beyond the current propositional core.
