# Iteration 013: Multi-Finding Source-Backed No-Orphan CPG Reports

Paper thread:

- Continues Yamaguchi, Golde, Arp, and Rieck, "Modeling and Discovering
  Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- Primary paper PDF: <https://www.ieee-security.org/TC/SP2014/papers/ModelingandDiscoveringVulnerabilitieswithCodePropertyGraphs.pdf>
- Joern CPG specification: <https://cpg.joern.io/>

## Core Claim

Iteration 012 lifted one no-orphan CPG finding to a source-backed report.  Real
SAST reports are batches.  This iteration lifts the no-orphan discipline to
multi-finding source-level CPG reports:

> Every source finding in the batch must be covered by a source/artifact
> provenance link, and every linked CPG artifact path must have checked
> extraction-origin coverage for all of its hops.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.SourceBackedNoOrphanCPG`: single source-backed no-orphan CPG runs.
- `PcSastLean.CPGNoOrphanAdapter`: artifact-level no-orphan CPG adapters.
- `PcSastLean.SourceBackedAdapters`: list-level source/artifact provenance
  through `MultiSourceBackedRun`.
- `PcSastLean.MultiAnalyzer`: sound aggregation of analyzer runs.

Gap before this iteration:

- Source-backed no-orphan CPG was single-entry.
- Multi-source provenance existed, but not specialized to no-orphan CPG entries.
- The theory did not yet prove that aggregate source-level CPG reports preserve
  hop-origin coverage entry by entry.

## Lean Patch

Added `PcSastLean.MultiSourceBackedNoOrphanCPG`.

New artifacts:

- `SourceBackedNoOrphanCPGEntry`: a no-orphan CPG finding certificate paired
  with a source/artifact sink provenance certificate.
- `sourceBackedNoOrphanCPGEntryRun`: the artifact run for one entry.
- `sourceBackedNoOrphanCPGEntryRuns`: artifact runs for a list of entries.
- `sourceBackedNoOrphanCPGEntryProvs`: source/artifact provenance links for a
  list of entries.
- `checkSourceBackedNoOrphanCPGEntries`: batch checker for entry certificates.
- `checkSourceBackedNoOrphanCPGEntries_sound`: accepted batch checking implies
  every entry's no-orphan CPG checker accepted.
- `sourceBackedNoOrphanCPGEntryRuns_sound`: every checked entry run is sound.
- `aggregateSourceBackedNoOrphanCPGEntries_sound`: the aggregate artifact run is
  sound.
- `sourceBackedNoOrphanCPGBatchRun`: source-level aggregate run via
  `MultiSourceBackedRun`.
- `sourceBackedNoOrphanCPGBatchRun_sound`: source-level soundness for the batch,
  given source/artifact provenance coverage and soundness.
- `sourceBackedNoOrphanCPGEntries_hops_have_origins`: every checked entry
  preserves per-hop extraction-origin evidence.

## What This Improves

The source-backed no-orphan story is no longer a one-finding demo.  A batch can
now expose the same two invariants entry by entry:

1. Source-level findings are covered by source/artifact provenance links.
2. Artifact-level CPG paths are no-orphan paths with typed extraction origins.

This is closer to a deployable SAST report format: one report, many findings,
each with its own checked provenance story.

## Remaining Gaps

- The batch theorem is not yet wired into a top-level `TriageRun`/CI
  no-bug-hiding demo.
- Source/artifact provenance soundness is still an obligation supplied to the
  theorem.
- The same demo CPG path is reused for two source sinks; richer examples should
  use distinct paths and distinct source spans.
- Real extraction algorithms still need to discharge origin correctness.

## Next Theorem Candidate

Connect multi-finding source-backed no-orphan CPG reports to the top-level CI
gate:

- build a `TriageRun` for the batch report;
- prove `ci_gate_no_bug_hiding` for the multi-source no-orphan CPG run;
- retain the theorem that every reported CPG path has per-hop extraction-origin
  coverage.
