# Iteration 012: Source-Backed No-Orphan CPG Reports

Paper thread:

- Continues Yamaguchi, Golde, Arp, and Rieck, "Modeling and Discovering
  Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- Primary paper PDF: <https://www.ieee-security.org/TC/SP2014/papers/ModelingandDiscoveringVulnerabilitieswithCodePropertyGraphs.pdf>
- Joern CPG specification: <https://cpg.joern.io/>

## Core Claim

Iteration 011 made no-orphan CPG evidence operational at the artifact analyzer
boundary.  This iteration lifts that property through the source-backed adapter:
a source-level CPG report can inherit both the source/artifact sink link and the
per-hop extraction-origin coverage of the underlying CPG path.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.SourceBackedAdapters`: maps artifact analyzer runs to source-level
  runs with `SourceSinkProv`.
- `PcSastLean.CPGNoOrphanAdapter`: builds artifact CPG runs only after every
  finding-path hop has checked extraction-origin provenance.
- `PcSastLean.CPGExtractionProvenance`: gives the typed AST/CFG/DDG/CDG/call/
  return origin witness language.

Gap before this iteration:

- No-orphan evidence stopped at the artifact-level CPG run.
- Source-backed CPG runs could show source/artifact sink soundness, but they did
  not expose the underlying hop-origin coverage.
- The source-level report boundary still looked separate from the CPG
  extraction-provenance boundary.

## Lean Patch

Added `PcSastLean.SourceBackedNoOrphanCPG`.

New artifacts:

- `sourceBackedNoOrphanCPGRun`: source-backed run built from a no-orphan CPG
  finding run.
- `sourceBackedNoOrphanCPGRun_sound`: source/artifact sink provenance plus a
  checked no-orphan CPG finding implies source-level analyzer soundness.
- `sourceBackedNoOrphanCPGRun_hops_have_origins`: the source-backed run still
  carries the theorem that every underlying CPG hop has an extraction origin.
- `sourceBackedNoOrphanOrderedSanitizerRun`: source-backed bridge for
  no-orphan ordered sanitizer runs.
- `sourceBackedNoOrphanOrderedSanitizerRun_sound`: source-level soundness for
  sanitized CPG runs built through the no-orphan adapter.
- `sourceBackedNoOrphanOrderedSanitizerRun_hops_have_origins`: ordered sanitizer
  source-backed runs inherit hop-origin coverage.

## What This Improves

The source-level CPG report boundary now has two independent proof obligations:

1. `SourceSinkProv.Sound`: if the source-level violation exists, the linked
   artifact sink exists.
2. `checkExtractedHops`: every hop in the underlying artifact CPG path has a
   typed extraction-origin certificate.

This does not verify a production extractor, but it prevents a weaker
integration mistake: dropping hop provenance when remapping artifact findings to
source-level reports.

## Remaining Gaps

- Only single-source provenance examples are modeled here; list-level
  source-backed no-orphan reports are next.
- Real source-map and generated-code provenance remain external.
- The origin facts are still checked, not derived from a real parser/CFG/DDG/CDG
  construction algorithm.
- Sanitized source-backed demo uses an empty concrete source violation list for
  the sanitized case; richer source-level sanitized semantics are future work.

## Next Theorem Candidate

Extend this to multi-finding source-backed no-orphan CPG reports:

- multiple source/artifact provenance links;
- multiple no-orphan CPG finding certificates;
- a theorem that every reported source violation is covered by a source link and
  every linked artifact CPG path has per-hop extraction-origin coverage.
