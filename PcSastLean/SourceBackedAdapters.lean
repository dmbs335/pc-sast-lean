import PcSastLean.CertificateAdapters

/-!
Source-backed certificate adapters.

`CertificateAdapters` lifted IFDS/CPG certificates into CI analyzer runs, but the
adapter only carried a sink id.  This module adds the missing provenance bridge:
an IR/graph sink is allowed to become a source-level CI finding only when a
source provenance certificate maps it to a source sink and the extraction layer
is sound.

Claim boundary:

* Verified here: artifact-level analyzer soundness plus source/artifact
  provenance yields source-level analyzer soundness for modeled violation lists.
* External obligations: real extractors must produce correct source locations,
  source spans, generated-code origins, and artifact/source sink links.
* Not modeled here: complete source-map semantics, macro/template expansion, or
  source-level parser correctness.
-/

namespace PcSastLean

structure SourceSinkProv where
  sourceSink : Node
  artifactSink : Node
  loc : SourceLoc
deriving DecidableEq, Repr

def SourceSinkProv.Sound
    (sourceViolations artifactViolations : List Node) (p : SourceSinkProv) : Prop :=
  p.sourceSink ∈ sourceViolations -> p.artifactSink ∈ artifactViolations

def SourceViolationsCoveredBy
    (sourceViolations : List Node) (p : SourceSinkProv) : Prop :=
  forall sink, sink ∈ sourceViolations -> sink = p.sourceSink

def SourceBackedRun
    (sourceViolations _artifactConcrete artifactAbstract : List Node)
    (prov : SourceSinkProv) : AnalyzerRun :=
  { concrete := sourceViolations
  , abstract := artifactAbstract.map (fun sink => if sink = prov.artifactSink then prov.sourceSink else sink)
  }

def ArtifactToSourceCovered
    (artifactAbstract : List Node) (prov : SourceSinkProv) : Prop :=
  forall sink, sink ∈ artifactAbstract -> sink = prov.artifactSink

def sourceBackedAbstract
    (artifactAbstract : List Node) (provs : List SourceSinkProv) : List Node :=
  (provs.filter (fun p => decide (p.artifactSink ∈ artifactAbstract))).map
    (fun p => p.sourceSink)

def SourceViolationsCoveredByAny
    (sourceViolations : List Node) (provs : List SourceSinkProv) : Prop :=
  forall sink, sink ∈ sourceViolations ->
    exists p, p ∈ provs /\ p.sourceSink = sink

def SourceProvsSound
    (sourceViolations artifactViolations : List Node)
    (provs : List SourceSinkProv) : Prop :=
  forall p, p ∈ provs -> SourceSinkProv.Sound sourceViolations artifactViolations p

def MultiSourceBackedRun
    (sourceViolations _artifactConcrete artifactAbstract : List Node)
    (provs : List SourceSinkProv) : AnalyzerRun :=
  { concrete := sourceViolations
  , abstract := sourceBackedAbstract artifactAbstract provs
  }

theorem sourceBackedRun_sound
    {sourceViolations artifactConcrete artifactAbstract : List Node}
    {prov : SourceSinkProv}
    (hsourceCovered : SourceViolationsCoveredBy sourceViolations prov)
    (hanalyzer : ListSubset artifactConcrete artifactAbstract)
    (hprov : SourceSinkProv.Sound sourceViolations artifactConcrete prov) :
    (SourceBackedRun sourceViolations artifactConcrete artifactAbstract prov).Sound := by
  intro sink hsource
  unfold SourceBackedRun
  have hsinkEq := hsourceCovered sink hsource
  subst hsinkEq
  have hartifact := hprov hsource
  have hcoveredArtifact := hanalyzer prov.artifactSink hartifact
  have hmap : prov.sourceSink ∈ artifactAbstract.map
      (fun s => if s = prov.artifactSink then prov.sourceSink else s) := by
    exact List.mem_map.mpr
      ⟨prov.artifactSink, hcoveredArtifact, by simp⟩
  exact hmap

theorem multiSourceBackedRun_sound
    {sourceViolations artifactConcrete artifactAbstract : List Node}
    {provs : List SourceSinkProv}
    (hsourceCovered : SourceViolationsCoveredByAny sourceViolations provs)
    (hanalyzer : ListSubset artifactConcrete artifactAbstract)
    (hprovs : SourceProvsSound sourceViolations artifactConcrete provs) :
    (MultiSourceBackedRun sourceViolations artifactConcrete artifactAbstract provs).Sound := by
  intro sink hsource
  unfold MultiSourceBackedRun
  rcases hsourceCovered sink hsource with ⟨p, hp, hsourceEq⟩
  have hpSource : p.sourceSink ∈ sourceViolations := by
    rw [hsourceEq]
    exact hsource
  have hartifactConcrete := hprovs p hp hpSource
  have hartifactAbstract := hanalyzer p.artifactSink hartifactConcrete
  unfold sourceBackedAbstract
  exact List.mem_map.mpr
    ⟨p, by simp [hp, hartifactAbstract], hsourceEq⟩

def sourceBackedIFDSRun
    (sourceViolations : List Node)
    (graph : List IFDSEdge) (seeds : List IFDSNode)
    (cert : IFDSCheckedCert) (projection : IFDSSinkProjection)
    (prov : SourceSinkProv) : AnalyzerRun :=
  SourceBackedRun sourceViolations
    (ifdsFindingRun graph seeds cert projection).concrete
    (ifdsFindingRun graph seeds cert projection).abstract
    prov

theorem sourceBackedIFDSRun_sound
    {sourceViolations : List Node}
    {graph : List IFDSEdge} {seeds : List IFDSNode}
    {cert : IFDSCheckedCert} {projection : IFDSSinkProjection} {prov : SourceSinkProv}
    (hcert : checkIFDSCert graph seeds cert = true)
    (hprojection : IFDSSinkProjection.Sound cert projection)
    (hsourceCovered : SourceViolationsCoveredBy sourceViolations prov)
    (hprov : SourceSinkProv.Sound sourceViolations
      (ifdsFindingRun graph seeds cert projection).concrete prov) :
    (sourceBackedIFDSRun sourceViolations graph seeds cert projection prov).Sound := by
  exact sourceBackedRun_sound hsourceCovered (ifdsFindingRun_sound hcert hprojection) hprov

def sourceBackedCPGRun
    (sourceViolations : List Node)
    (nodes : List CPGNode) (edges : List CPGEdge)
    (sources sinks : List CPGId) (cert : CPGFindingCert)
    (prov : SourceSinkProv) : AnalyzerRun :=
  SourceBackedRun sourceViolations
    (cpgFindingRun nodes edges sources sinks cert).concrete
    (cpgFindingRun nodes edges sources sinks cert).abstract
    prov

theorem sourceBackedCPGRun_sound
    {sourceViolations : List Node}
    {nodes : List CPGNode} {edges : List CPGEdge}
    {sources sinks : List CPGId} {cert : CPGFindingCert} {prov : SourceSinkProv}
    (hcert : checkCPGFinding nodes edges sources sinks cert = true)
    (hsourceCovered : SourceViolationsCoveredBy sourceViolations prov)
    (hprov : SourceSinkProv.Sound sourceViolations
      (cpgFindingRun nodes edges sources sinks cert).concrete prov) :
    (sourceBackedCPGRun sourceViolations nodes edges sources sinks cert prov).Sound := by
  exact sourceBackedRun_sound hsourceCovered (cpgFindingRun_sound hcert) hprov

/-! ## Demo -/

def sourceProvIFDS : SourceSinkProv :=
  { sourceSink := 9001, artifactSink := ifdsTargetSink ifdsCert.target, loc := demoLoc }

def sourceIFDSViolations : List Node := [9001]

theorem sourceIFDSCoveredBy :
    SourceViolationsCoveredBy sourceIFDSViolations sourceProvIFDS := by
  intro sink h
  simp [sourceIFDSViolations, sourceProvIFDS] at h
  exact h

theorem sourceIFDSProvSound :
    SourceSinkProv.Sound sourceIFDSViolations
      (ifdsFindingRun ifdsGraph [ifdsSeed] ifdsCert ifdsSinkProjection).concrete
      sourceProvIFDS := by
  intro h
  simp [sourceIFDSViolations, ifdsFindingRun, singletonFindingRun, sourceProvIFDS,
    ifdsTargetSink, ifdsCert] at h ⊢

def sourceBackedIFDSDemoRun : AnalyzerRun :=
  sourceBackedIFDSRun sourceIFDSViolations ifdsGraph [ifdsSeed] ifdsCert
    ifdsSinkProjection sourceProvIFDS

example : sourceBackedIFDSDemoRun.Sound :=
  sourceBackedIFDSRun_sound
    (by native_decide)
    ifdsSinkProjectionSound
    sourceIFDSCoveredBy
    sourceIFDSProvSound

def sourceProvCPG : SourceSinkProv :=
  { sourceSink := 9002, artifactSink := cpgCert.sink, loc := demoLoc }

def sourceCPGViolations : List Node := [9002]

theorem sourceCPGCoveredBy :
    SourceViolationsCoveredBy sourceCPGViolations sourceProvCPG := by
  intro sink h
  simp [sourceCPGViolations, sourceProvCPG] at h
  exact h

theorem sourceCPGProvSound :
    SourceSinkProv.Sound sourceCPGViolations
      (cpgFindingRun cpgNodes cpgEdges [1] [3] cpgCert).concrete
      sourceProvCPG := by
  intro h
  simp [sourceCPGViolations, cpgFindingRun, sourceProvCPG, cpgCert] at h ⊢

def sourceBackedCPGDemoRun : AnalyzerRun :=
  sourceBackedCPGRun sourceCPGViolations cpgNodes cpgEdges [1] [3] cpgCert sourceProvCPG

example : sourceBackedCPGDemoRun.Sound :=
  sourceBackedCPGRun_sound
    (by native_decide)
    sourceCPGCoveredBy
    sourceCPGProvSound

def multiSourceViolations : List Node := [9001, 9002]

def multiSourceProvs : List SourceSinkProv := [sourceProvIFDS, sourceProvCPG]

theorem multiSourceCoveredBy :
    SourceViolationsCoveredByAny multiSourceViolations multiSourceProvs := by
  intro sink h
  simp [multiSourceViolations] at h
  cases h with
  | inl hifds =>
      subst hifds
      exact ⟨sourceProvIFDS, by simp [multiSourceProvs], by simp [sourceProvIFDS]⟩
  | inr hcpg =>
      subst hcpg
      exact ⟨sourceProvCPG, by simp [multiSourceProvs], by simp [sourceProvCPG]⟩

def multiArtifactRun : AnalyzerRun :=
  aggregateRuns [ifdsAdapterRun, cpgAdapterRun]

theorem multiArtifactRunSound : multiArtifactRun.Sound := by
  unfold multiArtifactRun
  exact aggregateRuns_sound
    (by
      intro r hr
      have hcases : r = ifdsAdapterRun ∨ r = cpgAdapterRun := by
        simpa using hr
      cases hcases with
      | inl hifds =>
          subst hifds
          exact ifdsAdapterRunSound
      | inr hcpg =>
          subst hcpg
          exact cpgAdapterRunSound)

theorem multiSourceProvsSound :
    SourceProvsSound multiSourceViolations multiArtifactRun.concrete multiSourceProvs := by
  intro p hp hsource
  have hpCases : p = sourceProvIFDS ∨ p = sourceProvCPG := by
    simpa [multiSourceProvs] using hp
  cases hpCases with
  | inl hifds =>
      subst hifds
      simp [multiSourceViolations, multiArtifactRun, aggregateRuns, unionNodes,
        ifdsAdapterRun, ifdsFindingRun, singletonFindingRun, sourceProvIFDS,
        ifdsTargetSink, ifdsCert] at hsource ⊢
  | inr hcpg =>
      subst hcpg
      simp [multiSourceViolations, multiArtifactRun, aggregateRuns, unionNodes,
        cpgAdapterRun, cpgFindingRun, sourceProvCPG, cpgCert] at hsource ⊢

def multiSourceBackedDemoRun : AnalyzerRun :=
  MultiSourceBackedRun multiSourceViolations multiArtifactRun.concrete
    multiArtifactRun.abstract multiSourceProvs

example : multiSourceBackedDemoRun.Sound := by
  exact multiSourceBackedRun_sound
    multiSourceCoveredBy
    multiArtifactRunSound
    multiSourceProvsSound

def sourceBackedTriage : TriageRun :=
  { report := [9001], suppressed := [], evidence := [] }

theorem sourceBackedTriageComplete :
    sourceBackedTriage.Complete sourceBackedIFDSDemoRun := by
  intro sink h
  left
  simpa [sourceBackedIFDSDemoRun, sourceBackedIFDSRun, SourceBackedRun,
    ifdsFindingRun, singletonFindingRun, sourceProvIFDS, sourceBackedTriage] using h

example : ListSubset sourceBackedIFDSDemoRun.concrete sourceBackedTriage.report :=
  ci_gate_no_bug_hiding
    (sourceBackedIFDSRun_sound
      (by native_decide)
      ifdsSinkProjectionSound
      sourceIFDSCoveredBy
      sourceIFDSProvSound)
    sourceBackedTriageComplete

end PcSastLean
