import PcSastLean.MultiAnalyzer
import PcSastLean.IFDSSummary

/-!
Certificate adapters.

This module lifts IFDS/CPG certificates into `AnalyzerRun`s so the top-level
multi-analyzer CI theorem can consume them.  A path/finding certificate produces
an abstract finding.  A fixpoint/no-reach certificate justifies absence, so it
produces no concrete/abstract finding for that target.

Claim boundary:

* Verified here: accepted IFDS/CPG certificate artifacts can be lifted to the
  common CI interface without changing the checked target sink.
* External obligations: certificate producers and sink projections must be
  supplied by an analyzer/extractor.
* Not modeled here: whether the external scanner found all relevant findings or
  ranked them well.
-/

namespace PcSastLean

def singletonFindingRun (sink : Node) : AnalyzerRun :=
  { concrete := [sink], abstract := [sink] }

theorem singletonFindingRun_sound (sink : Node) :
    (singletonFindingRun sink).Sound := by
  intro id h
  exact h

def ifdsTargetSink (target : IFDSNode) : Node :=
  target.point

structure IFDSSinkProjection where
  target : IFDSNode
  sink : Node
  loc : SourceLoc
deriving DecidableEq, Repr

def IFDSSinkProjection.Sound
    (cert : IFDSCheckedCert) (projection : IFDSSinkProjection) : Prop :=
  projection.target = cert.target /\
  projection.sink = ifdsTargetSink cert.target

def IFDSSinkProjection.SoundCompressed
    (cert : IFDSCompressedCert) (projection : IFDSSinkProjection) : Prop :=
  projection.target = cert.target /\
  projection.sink = ifdsTargetSink cert.target

def ifdsFindingRun
    (_graph : List IFDSEdge) (_seeds : List IFDSNode)
    (cert : IFDSCheckedCert) (_projection : IFDSSinkProjection) : AnalyzerRun :=
  singletonFindingRun (ifdsTargetSink cert.target)

theorem ifdsFindingRun_sound
    {graph : List IFDSEdge} {seeds : List IFDSNode}
    {cert : IFDSCheckedCert} {projection : IFDSSinkProjection}
    (hcert : checkIFDSCert graph seeds cert = true)
    (hprojection : IFDSSinkProjection.Sound cert projection) :
    (ifdsFindingRun graph seeds cert projection).Sound := by
  have _hreach := checked_ifds_cert_sound hcert
  have _hprojectedTarget : projection.target = cert.target := hprojection.left
  have _hprojectedSink : projection.sink = ifdsTargetSink cert.target := hprojection.right
  exact singletonFindingRun_sound (ifdsTargetSink cert.target)

theorem ifdsFindingRun_reports_only_target_sink
    {graph : List IFDSEdge} {seeds : List IFDSNode}
    {cert : IFDSCheckedCert} {projection : IFDSSinkProjection}
    {sink : Node}
    (h : sink ∈ (ifdsFindingRun graph seeds cert projection).abstract) :
    sink = ifdsTargetSink cert.target := by
  simpa [ifdsFindingRun, singletonFindingRun] using h

def ifdsCompressedFindingRun
    (_graph : List IFDSEdge) (_seeds : List IFDSNode)
    (cert : IFDSCompressedCert) (_projection : IFDSSinkProjection) : AnalyzerRun :=
  singletonFindingRun (ifdsTargetSink cert.target)

theorem ifdsCompressedFindingRun_sound
    {graph : List IFDSEdge} {seeds : List IFDSNode}
    {cert : IFDSCompressedCert} {projection : IFDSSinkProjection}
    (hcert : checkIFDSCompressedCert graph seeds cert = true)
    (hprojection : IFDSSinkProjection.SoundCompressed cert projection) :
    (ifdsCompressedFindingRun graph seeds cert projection).Sound := by
  have _hreach := checked_ifds_compressed_cert_sound hcert
  have _hprojectedTarget : projection.target = cert.target := hprojection.left
  have _hprojectedSink : projection.sink = ifdsTargetSink cert.target := hprojection.right
  exact singletonFindingRun_sound (ifdsTargetSink cert.target)

theorem ifdsCompressedFindingRun_reports_only_target_sink
    {graph : List IFDSEdge} {seeds : List IFDSNode}
    {cert : IFDSCompressedCert} {projection : IFDSSinkProjection}
    {sink : Node}
    (h : sink ∈ (ifdsCompressedFindingRun graph seeds cert projection).abstract) :
    sink = ifdsTargetSink cert.target := by
  simpa [ifdsCompressedFindingRun, singletonFindingRun] using h

def ifdsNoFindingRun
    (_graph : List IFDSEdge) (_seeds : List IFDSNode)
    (_target : IFDSNode) (_cert : IFDSFixpointCert) : AnalyzerRun :=
  { concrete := [], abstract := [] }

theorem ifdsNoFindingRun_sound
    {graph : List IFDSEdge} {seeds : List IFDSNode}
    {target : IFDSNode} {cert : IFDSFixpointCert}
    (hcheck : checkIFDSFixpoint graph seeds cert = true)
    (hnot : target ∉ cert.reached) :
    (ifdsNoFindingRun graph seeds target cert).Sound := by
  have _hnoreach := checked_ifds_no_reach (target := target) hcheck hnot
  intro id h
  simp [ifdsNoFindingRun] at h

def cpgFindingRun
    (_nodes : List CPGNode) (_edges : List CPGEdge)
    (_sources _sinks : List CPGId) (cert : CPGFindingCert) : AnalyzerRun :=
  { concrete := [cert.sink], abstract := [cert.sink] }

theorem cpgFindingRun_sound
    {nodes : List CPGNode} {edges : List CPGEdge}
    {sources sinks : List CPGId} {cert : CPGFindingCert}
    (hcert : checkCPGFinding nodes edges sources sinks cert = true) :
    (cpgFindingRun nodes edges sources sinks cert).Sound := by
  have _hfinding := checked_cpg_finding_sound hcert
  intro id h
  exact h

theorem cpgFindingRun_reports_only_cert_sink
    {nodes : List CPGNode} {edges : List CPGEdge}
    {sources sinks : List CPGId} {cert : CPGFindingCert}
    {sink : Node}
    (h : sink ∈ (cpgFindingRun nodes edges sources sinks cert).abstract) :
    sink = cert.sink := by
  simpa [cpgFindingRun] using h

/-! ## Demo: aggregate IFDS + CPG finding runs -/

def ifdsSinkProjection : IFDSSinkProjection :=
  { target := ifdsCert.target
  , sink := ifdsTargetSink ifdsCert.target
  , loc := demoLoc
  }

theorem ifdsSinkProjectionSound :
    IFDSSinkProjection.Sound ifdsCert ifdsSinkProjection := by
  simp [IFDSSinkProjection.Sound, ifdsSinkProjection]

def ifdsCompressedSinkProjection : IFDSSinkProjection :=
  { target := ifdsCompressedCert.target
  , sink := ifdsTargetSink ifdsCompressedCert.target
  , loc := demoLoc
  }

theorem ifdsCompressedSinkProjectionSound :
    IFDSSinkProjection.SoundCompressed ifdsCompressedCert ifdsCompressedSinkProjection := by
  simp [IFDSSinkProjection.SoundCompressed, ifdsCompressedSinkProjection]

def ifdsAdapterRun : AnalyzerRun :=
  ifdsFindingRun ifdsGraph [ifdsSeed] ifdsCert ifdsSinkProjection

def cpgAdapterRun : AnalyzerRun :=
  cpgFindingRun cpgNodes cpgEdges [1] [3] cpgCert

theorem ifdsAdapterRunSound : ifdsAdapterRun.Sound :=
  ifdsFindingRun_sound (by native_decide) ifdsSinkProjectionSound

def ifdsCompressedAdapterRun : AnalyzerRun :=
  ifdsCompressedFindingRun ifdsGraph [ifdsSeed] ifdsCompressedCert ifdsCompressedSinkProjection

theorem ifdsCompressedAdapterRunSound : ifdsCompressedAdapterRun.Sound :=
  ifdsCompressedFindingRun_sound (by native_decide) ifdsCompressedSinkProjectionSound

theorem cpgAdapterRunSound : cpgAdapterRun.Sound :=
  cpgFindingRun_sound (by native_decide)

def adapterTriage : TriageRun :=
  { report := (aggregateRuns [ifdsAdapterRun, cpgAdapterRun]).abstract
  , suppressed := []
  , evidence := []
  }

theorem adapterTriageComplete :
    adapterTriage.Complete (aggregateRuns [ifdsAdapterRun, cpgAdapterRun]) := by
  intro sink h
  left
  exact h

example :
    ListSubset
      (aggregateRuns [ifdsAdapterRun, cpgAdapterRun]).concrete
      adapterTriage.report :=
  aggregate_ci_gate_no_bug_hiding
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
    adapterTriageComplete

end PcSastLean
