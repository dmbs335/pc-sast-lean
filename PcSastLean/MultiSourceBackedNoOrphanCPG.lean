import PcSastLean.SourceBackedNoOrphanCPG

/-!
Multi-finding source-backed no-orphan CPG reports.

`SourceBackedNoOrphanCPG` handles one source/artifact CPG link at a time.  Real
SAST reports contain many findings.  This module packages a list of no-orphan
CPG finding certificates together with source/artifact provenance links and
shows that the aggregate source-level run preserves both:

* source-level analyzer soundness, and
* per-hop extraction-origin coverage for every linked CPG path.

Claim boundary:

* Verified here: if each no-orphan CPG entry checks, the aggregate artifact run
  is sound; if source/artifact provenance covers the source findings, the
  source-level aggregate run is sound; every checked entry keeps hop-origin
  evidence.
* External obligations: real extractors still need to prove source/artifact sink
  provenance and the correctness of extraction-origin facts.
* Not modeled here: finding completeness, source-map completeness, generated
  code expansion, real parser/CFG/DDG/CDG algorithms, or ranking.
-/

namespace PcSastLean

structure SourceBackedNoOrphanCPGEntry where
  cert : CPGNoOrphanFindingCert
  prov : SourceSinkProv
deriving Repr

def sourceBackedNoOrphanCPGEntryRun
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (entry : SourceBackedNoOrphanCPGEntry) : AnalyzerRun :=
  cpgNoOrphanFindingRun nodes components sources sinks entry.cert

def sourceBackedNoOrphanCPGEntryRuns
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (entries : List SourceBackedNoOrphanCPGEntry) : List AnalyzerRun :=
  entries.map (sourceBackedNoOrphanCPGEntryRun nodes components sources sinks)

def sourceBackedNoOrphanCPGEntryProvs
    (entries : List SourceBackedNoOrphanCPGEntry) : List SourceSinkProv :=
  entries.map (fun entry => entry.prov)

def checkSourceBackedNoOrphanCPGEntry
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (entry : SourceBackedNoOrphanCPGEntry) : Bool :=
  checkCPGNoOrphanFinding nodes components sources sinks entry.cert

def checkSourceBackedNoOrphanCPGEntries
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId) :
    List SourceBackedNoOrphanCPGEntry -> Bool
  | [] => true
  | entry :: rest =>
      checkSourceBackedNoOrphanCPGEntry nodes components sources sinks entry &&
      checkSourceBackedNoOrphanCPGEntries nodes components sources sinks rest

def sourceBackedNoOrphanCPGBatchRun
    (sourceViolations : List Node)
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (entries : List SourceBackedNoOrphanCPGEntry) : AnalyzerRun :=
  let artifactRun :=
    aggregateRuns
      (sourceBackedNoOrphanCPGEntryRuns nodes components sources sinks entries)
  MultiSourceBackedRun sourceViolations artifactRun.concrete artifactRun.abstract
    (sourceBackedNoOrphanCPGEntryProvs entries)

def SourceBackedNoOrphanCPGEntriesChecked
    (nodes : List CPGNode) (components : List CPGComponentEdge)
    (sources sinks : List CPGId)
    (entries : List SourceBackedNoOrphanCPGEntry) : Prop :=
  forall entry, entry ∈ entries ->
    checkSourceBackedNoOrphanCPGEntry nodes components sources sinks entry = true

theorem checkSourceBackedNoOrphanCPGEntries_sound
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId} :
    forall {entries : List SourceBackedNoOrphanCPGEntry},
      checkSourceBackedNoOrphanCPGEntries
        nodes components sources sinks entries = true ->
      SourceBackedNoOrphanCPGEntriesChecked
        nodes components sources sinks entries := by
  intro entries
  induction entries with
  | nil =>
      intro _ entry hmem
      simp at hmem
  | cons head rest ih =>
      intro hcheck entry hmem
      simp [checkSourceBackedNoOrphanCPGEntries] at hcheck
      simp at hmem
      cases hmem with
      | inl hhead =>
          subst hhead
          exact hcheck.left
      | inr htail =>
          exact ih hcheck.right entry htail

theorem sourceBackedNoOrphanCPGEntryRuns_sound
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId}
    {entries : List SourceBackedNoOrphanCPGEntry}
    (hchecked :
      SourceBackedNoOrphanCPGEntriesChecked
        nodes components sources sinks entries) :
    forall run,
      run ∈ sourceBackedNoOrphanCPGEntryRuns
        nodes components sources sinks entries ->
      run.Sound := by
  intro run hrun
  unfold sourceBackedNoOrphanCPGEntryRuns at hrun
  rcases List.mem_map.mp hrun with ⟨entry, hentry, hrunEq⟩
  subst hrunEq
  exact cpgNoOrphanFindingRun_sound (hchecked entry hentry)

theorem aggregateSourceBackedNoOrphanCPGEntries_sound
    {nodes : List CPGNode} {components : List CPGComponentEdge}
    {sources sinks : List CPGId}
    {entries : List SourceBackedNoOrphanCPGEntry}
    (hchecked :
      SourceBackedNoOrphanCPGEntriesChecked
        nodes components sources sinks entries) :
    (aggregateRuns
      (sourceBackedNoOrphanCPGEntryRuns
        nodes components sources sinks entries)).Sound := by
  exact aggregateRuns_sound
    (sourceBackedNoOrphanCPGEntryRuns_sound hchecked)

theorem sourceBackedNoOrphanCPGBatchRun_sound
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
    (sourceBackedNoOrphanCPGBatchRun
      sourceViolations nodes components sources sinks entries).Sound := by
  unfold sourceBackedNoOrphanCPGBatchRun
  exact multiSourceBackedRun_sound
    hsourceCovered
    (aggregateSourceBackedNoOrphanCPGEntries_sound hchecked)
    hprovs

theorem sourceBackedNoOrphanCPGEntries_hops_have_origins
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
  intro entry hentry hop hhop
  exact cpgNoOrphanFindingRun_hops_have_origins
    (nodes := nodes)
    (components := components)
    (sources := sources)
    (sinks := sinks)
    (cert := entry.cert)
    (hchecked entry hentry)
    hop
    hhop

/-! ## Demo: two source findings backed by no-orphan CPG paths -/

def sourceProvNoOrphanCPGAlt : SourceSinkProv :=
  { sourceSink := 9021
  , artifactSink := cpgNoOrphanFindingCert.finding.sink
  , loc := demoLoc
  }

def sourceBackedNoOrphanCPGEntryA : SourceBackedNoOrphanCPGEntry :=
  { cert := cpgNoOrphanFindingCert
  , prov := sourceProvNoOrphanCPG
  }

def sourceBackedNoOrphanCPGEntryB : SourceBackedNoOrphanCPGEntry :=
  { cert := cpgNoOrphanFindingCert
  , prov := sourceProvNoOrphanCPGAlt
  }

def sourceBackedNoOrphanCPGEntries : List SourceBackedNoOrphanCPGEntry :=
  [sourceBackedNoOrphanCPGEntryA, sourceBackedNoOrphanCPGEntryB]

def multiNoOrphanSourceViolations : List Node := [9010, 9021]

example :
    checkSourceBackedNoOrphanCPGEntries
      cpgTraversalNodes cpgComponentGraph
      cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
      sourceBackedNoOrphanCPGEntries = true := by
  native_decide

theorem multiNoOrphanSourceCoveredBy :
    SourceViolationsCoveredByAny
      multiNoOrphanSourceViolations
      (sourceBackedNoOrphanCPGEntryProvs
        sourceBackedNoOrphanCPGEntries) := by
  intro sink h
  simp [multiNoOrphanSourceViolations] at h
  cases h with
  | inl hfirst =>
      subst hfirst
      exact ⟨sourceProvNoOrphanCPG, by
        simp [sourceBackedNoOrphanCPGEntryProvs,
          sourceBackedNoOrphanCPGEntries, sourceBackedNoOrphanCPGEntryA,
          sourceBackedNoOrphanCPGEntryB], by
        simp [sourceProvNoOrphanCPG]⟩
  | inr hrest =>
      subst hrest
      exact ⟨sourceProvNoOrphanCPGAlt, by
        simp [sourceBackedNoOrphanCPGEntryProvs,
          sourceBackedNoOrphanCPGEntries, sourceBackedNoOrphanCPGEntryA,
          sourceBackedNoOrphanCPGEntryB], by
        simp [sourceProvNoOrphanCPGAlt]⟩

theorem multiNoOrphanSourceProvsSound :
    SourceProvsSound multiNoOrphanSourceViolations
      (aggregateRuns
        (sourceBackedNoOrphanCPGEntryRuns
          cpgTraversalNodes cpgComponentGraph
          cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
          sourceBackedNoOrphanCPGEntries)).concrete
      (sourceBackedNoOrphanCPGEntryProvs
        sourceBackedNoOrphanCPGEntries) := by
  intro p hp _hsource
  have hpCases :
      p = sourceProvNoOrphanCPG ∨ p = sourceProvNoOrphanCPGAlt := by
    simpa [sourceBackedNoOrphanCPGEntryProvs,
      sourceBackedNoOrphanCPGEntries, sourceBackedNoOrphanCPGEntryA,
      sourceBackedNoOrphanCPGEntryB] using hp
  cases hpCases with
  | inl hfirst =>
      subst hfirst
      simp [sourceBackedNoOrphanCPGEntryRuns,
        sourceBackedNoOrphanCPGEntryRun, aggregateRuns, unionNodes,
        cpgNoOrphanFindingRun, sourceProvNoOrphanCPG,
        sourceBackedNoOrphanCPGEntries, sourceBackedNoOrphanCPGEntryA,
        sourceBackedNoOrphanCPGEntryB, cpgNoOrphanFindingCert,
        cpgAstCfgDataCert]
  | inr hsecond =>
      subst hsecond
      simp [sourceBackedNoOrphanCPGEntryRuns,
        sourceBackedNoOrphanCPGEntryRun, aggregateRuns, unionNodes,
        cpgNoOrphanFindingRun, sourceProvNoOrphanCPGAlt,
        sourceBackedNoOrphanCPGEntries, sourceBackedNoOrphanCPGEntryA,
        sourceBackedNoOrphanCPGEntryB, cpgNoOrphanFindingCert,
        cpgAstCfgDataCert]

def multiSourceBackedNoOrphanCPGDemoRun : AnalyzerRun :=
  sourceBackedNoOrphanCPGBatchRun
    multiNoOrphanSourceViolations
    cpgTraversalNodes cpgComponentGraph
    cpgAstCfgDataQuery.sources cpgAstCfgDataQuery.sinks
    sourceBackedNoOrphanCPGEntries

example : multiSourceBackedNoOrphanCPGDemoRun.Sound :=
  sourceBackedNoOrphanCPGBatchRun_sound
    (checkSourceBackedNoOrphanCPGEntries_sound (by native_decide))
    multiNoOrphanSourceCoveredBy
    multiNoOrphanSourceProvsSound

example :
    forall entry, entry ∈ sourceBackedNoOrphanCPGEntries ->
      forall hop, hop ∈ entry.cert.finding.hops ->
        exists origin : CPGExtractionOrigin,
          hop.kind = origin.componentKind.toEdgeKind /\
          hop.edge = origin.toComponentEdge.toCPGEdge :=
  sourceBackedNoOrphanCPGEntries_hops_have_origins
    (nodes := cpgTraversalNodes)
    (components := cpgComponentGraph)
    (sources := cpgAstCfgDataQuery.sources)
    (sinks := cpgAstCfgDataQuery.sinks)
    (entries := sourceBackedNoOrphanCPGEntries)
    (checkSourceBackedNoOrphanCPGEntries_sound (by native_decide))

end PcSastLean
