import PcSastLean.MultiSourceBackedNoOrphanCPG

/-!
CI gate for multi-source no-orphan CPG reports.

`MultiSourceBackedNoOrphanCPG` proves that a batch source-level CPG analyzer run
is sound and preserves per-hop extraction-origin coverage for every checked CPG
entry.  This module attaches the top-level CI theorem: if the triage report is
the checked source-level abstract report, then no modeled concrete source bug is
hidden, and the CPG path-origin evidence is still available entry by entry.

Claim boundary:

* Verified here: checked multi-source no-orphan CPG batches compose with
  `ci_gate_no_bug_hiding`, and the same CI package exposes per-hop extraction
  origins for every CPG entry.
* External obligations: source/artifact provenance and extraction-origin
  correctness are still supplied by the extractor/analyzer.
* Not modeled here: ranking, suppression UX, production query compilation,
  source-map completeness, or analyzer recall.
-/

namespace PcSastLean

def sourceBackedNoOrphanCPGBatchTriage
    (sourceViolations : List Node)
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (entries : List SourceBackedNoOrphanCPGEntry) : TriageRun :=
  { report :=
      (sourceBackedNoOrphanCPGBatchRun
        sourceViolations nodes components sources sinks entries).abstract
  , suppressed := []
  , evidence := []
  }

theorem sourceBackedNoOrphanCPGBatchTriage_complete
    (sourceViolations : List Node)
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (entries : List SourceBackedNoOrphanCPGEntry) :
    (sourceBackedNoOrphanCPGBatchTriage
      sourceViolations nodes components sources sinks entries).Complete
      (sourceBackedNoOrphanCPGBatchRun
        sourceViolations nodes components sources sinks entries) := by
  intro sink habstract
  left
  simpa [sourceBackedNoOrphanCPGBatchTriage] using habstract

theorem sourceBackedNoOrphanCPGBatch_ci_no_bug_hiding
    {sourceViolations : List Node}
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId}
    {entries : List SourceBackedNoOrphanCPGEntry}
    (hchecked :
      SourceBackedNoOrphanCPGEntriesChecked
        nodes components sources sinks entries)
    (hsourceCovered :
      SourceViolationsCoveredByAny sourceViolations
        (sourceBackedNoOrphanCPGEntryProvs entries))
    (hprovs :
      SourceProvsSound sourceViolations
        (aggregateRuns
          (sourceBackedNoOrphanCPGEntryRuns
            nodes components sources sinks entries)).concrete
        (sourceBackedNoOrphanCPGEntryProvs entries)) :
    ListSubset
      (sourceBackedNoOrphanCPGBatchRun
        sourceViolations nodes components sources sinks entries).concrete
      (sourceBackedNoOrphanCPGBatchTriage
        sourceViolations nodes components sources sinks entries).report := by
  exact ci_gate_no_bug_hiding
    (sourceBackedNoOrphanCPGBatchRun_sound hchecked hsourceCovered hprovs)
    (sourceBackedNoOrphanCPGBatchTriage_complete
      sourceViolations nodes components sources sinks entries)

theorem sourceBackedNoOrphanCPGBatch_ci_not_reported_not_concrete
    {sourceViolations : List Node}
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId}
    {entries : List SourceBackedNoOrphanCPGEntry}
    {sink : Node}
    (hchecked :
      SourceBackedNoOrphanCPGEntriesChecked
        nodes components sources sinks entries)
    (hsourceCovered :
      SourceViolationsCoveredByAny sourceViolations
        (sourceBackedNoOrphanCPGEntryProvs entries))
    (hprovs :
      SourceProvsSound sourceViolations
        (aggregateRuns
          (sourceBackedNoOrphanCPGEntryRuns
            nodes components sources sinks entries)).concrete
        (sourceBackedNoOrphanCPGEntryProvs entries))
    (hnot :
      sink ∉ (sourceBackedNoOrphanCPGBatchTriage
        sourceViolations nodes components sources sinks entries).report) :
    sink ∉
      (sourceBackedNoOrphanCPGBatchRun
        sourceViolations nodes components sources sinks entries).concrete := by
  exact ci_gate_not_reported_not_concrete
    (sourceBackedNoOrphanCPGBatchRun_sound hchecked hsourceCovered hprovs)
    (sourceBackedNoOrphanCPGBatchTriage_complete
      sourceViolations nodes components sources sinks entries)
    hnot

theorem sourceBackedNoOrphanCPGBatch_ci_hops_have_origins
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId}
    {entries : List SourceBackedNoOrphanCPGEntry}
    (hchecked :
      SourceBackedNoOrphanCPGEntriesChecked
        nodes components sources sinks entries) :
    forall entry, entry ∈ entries ->
      forall hop, hop ∈ entry.cert.finding.hops ->
        exists origin : CPGExtractionOrigin,
          hop.kind = origin.componentKind.toEdgeKind /\
          hop.edge = origin.toComponentEdge.toCPGEdge := by
  exact sourceBackedNoOrphanCPGEntries_hops_have_origins hchecked

theorem sourceBackedNoOrphanCPGBatch_ci_report_and_origins
    {sourceViolations : List Node}
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId}
    {entries : List SourceBackedNoOrphanCPGEntry}
    (hchecked :
      SourceBackedNoOrphanCPGEntriesChecked
        nodes components sources sinks entries)
    (hsourceCovered :
      SourceViolationsCoveredByAny sourceViolations
        (sourceBackedNoOrphanCPGEntryProvs entries))
    (hprovs :
      SourceProvsSound sourceViolations
        (aggregateRuns
          (sourceBackedNoOrphanCPGEntryRuns
            nodes components sources sinks entries)).concrete
        (sourceBackedNoOrphanCPGEntryProvs entries)) :
    ListSubset
      (sourceBackedNoOrphanCPGBatchRun
        sourceViolations nodes components sources sinks entries).concrete
      (sourceBackedNoOrphanCPGBatchTriage
        sourceViolations nodes components sources sinks entries).report /\
    forall entry, entry ∈ entries ->
      forall hop, hop ∈ entry.cert.finding.hops ->
        exists origin : CPGExtractionOrigin,
          hop.kind = origin.componentKind.toEdgeKind /\
          hop.edge = origin.toComponentEdge.toCPGEdge := by
  exact ⟨
    sourceBackedNoOrphanCPGBatch_ci_no_bug_hiding
      hchecked hsourceCovered hprovs,
    sourceBackedNoOrphanCPGBatch_ci_hops_have_origins hchecked
  ⟩

/-! ## Demo: CI report for the multi-source no-orphan CPG batch -/

def multiSourceBackedNoOrphanCPGDemoTriage : TriageRun :=
  sourceBackedNoOrphanCPGBatchTriage
    multiNoOrphanSourceViolations
    cpgTraversalNodes cpgComponentGraph
    cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
    sourceBackedNoOrphanCPGEntries

theorem multiSourceBackedNoOrphanCPGDemoTriageComplete :
    multiSourceBackedNoOrphanCPGDemoTriage.Complete
      multiSourceBackedNoOrphanCPGDemoRun := by
  unfold multiSourceBackedNoOrphanCPGDemoTriage
  unfold multiSourceBackedNoOrphanCPGDemoRun
  exact sourceBackedNoOrphanCPGBatchTriage_complete
    multiNoOrphanSourceViolations
    cpgTraversalNodes cpgComponentGraph
    cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
    sourceBackedNoOrphanCPGEntries

example :
    ListSubset
      multiSourceBackedNoOrphanCPGDemoRun.concrete
      multiSourceBackedNoOrphanCPGDemoTriage.report :=
  sourceBackedNoOrphanCPGBatch_ci_no_bug_hiding
    (checkSourceBackedNoOrphanCPGEntries_sound (by native_decide))
    multiNoOrphanSourceCoveredBy
    multiNoOrphanSourceProvsSound

example :
    ListSubset
      multiSourceBackedNoOrphanCPGDemoRun.concrete
      multiSourceBackedNoOrphanCPGDemoTriage.report /\
    forall entry, entry ∈ sourceBackedNoOrphanCPGEntries ->
      forall hop, hop ∈ entry.cert.finding.hops ->
        exists origin : CPGExtractionOrigin,
          hop.kind = origin.componentKind.toEdgeKind /\
          hop.edge = origin.toComponentEdge.toCPGEdge :=
  sourceBackedNoOrphanCPGBatch_ci_report_and_origins
    (checkSourceBackedNoOrphanCPGEntries_sound (by native_decide))
    multiNoOrphanSourceCoveredBy
    multiNoOrphanSourceProvsSound

end PcSastLean
