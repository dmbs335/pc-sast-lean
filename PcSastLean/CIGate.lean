import PcSastLean.NoBugHiding

/-!
Top-level CI gate.

This module packages the previous gates into a single CI-facing theorem.  A
scanner family supplies concrete and abstract violation lists plus a soundness
proof.  Triage supplies a final report plus proof-carrying suppressions.  Lean
then proves that every concrete bug from that scanner family is still in the
final report.

Claim boundary:

* Verified here: sound analyzer results plus complete proof-carrying triage imply
  no modeled concrete bug is hidden from the final report.
* External obligations: analyzers must supply soundness proofs/certificates, and
  source-level use also requires extraction/provenance obligations.
* Not modeled here: ranking quality, developer UX, precision, recall, or
  production scanner implementation correctness.
-/

namespace PcSastLean

structure AnalyzerRun where
  concrete : List Node
  abstract : List Node

def AnalyzerRun.Sound (r : AnalyzerRun) : Prop :=
  ListSubset r.concrete r.abstract

structure TriageRun where
  report : List Node
  suppressed : List Node
  evidence : List TriageEvidence

def TriageRun.Complete (r : AnalyzerRun) (t : TriageRun) : Prop :=
  TriageComplete r.abstract t.report t.suppressed t.evidence r.concrete

theorem ci_gate_no_bug_hiding
    {run : AnalyzerRun} {triage : TriageRun}
    (hsound : run.Sound)
    (hcomplete : triage.Complete run) :
    ListSubset run.concrete triage.report := by
  exact no_bug_hiding hsound hcomplete

theorem ci_gate_not_reported_not_concrete
    {run : AnalyzerRun} {triage : TriageRun} {sink : Node}
    (hsound : run.Sound)
    (hcomplete : triage.Complete run)
    (hnot : sink ∉ triage.report) :
    sink ∉ run.concrete := by
  exact no_bug_hiding_not_reported hsound hcomplete hnot

/-! ## Analyzer-family adapters -/

def heapAnalyzerRun
    (concrete : ConcreteHeapState) (abstract : AbsHeapState) (prog : List HInstr) :
    AnalyzerRun :=
  { concrete := (execConcreteHeap concrete prog).2
  , abstract := (execAbsHeap abstract prog).2
  }

theorem heapAnalyzerRun_sound
    {concrete : ConcreteHeapState} {abstract : AbsHeapState} {prog : List HInstr}
    (hs : HeapSound concrete abstract) :
    (heapAnalyzerRun concrete abstract prog).Sound := by
  exact (execHeap_sound prog hs).right

def sanitizerAnalyzerRun
    (concrete abstract : SecStore) (prog : List SInstr) : AnalyzerRun :=
  { concrete := (sexec concrete prog).2
  , abstract := (sexec abstract prog).2
  }

theorem sanitizerAnalyzerRun_sound
    {concrete abstract : SecStore} {prog : List SInstr}
    (hs : SecStore.Sound concrete abstract) :
    (sanitizerAnalyzerRun concrete abstract prog).Sound := by
  exact (sexec_sound prog hs).right

def frameworkAnalyzerRun
    (routes : List RouteEntry) (routeMap : RouteKey -> List HandlerId)
    (concrete abstract : HandlerViolations) (req : Request) : AnalyzerRun :=
  { concrete := execConcreteRequest routes concrete req
  , abstract := execAbstractRequest routeMap abstract req
  }

theorem frameworkAnalyzerRun_sound
    {routes : List RouteEntry} {routeMap : RouteKey -> List HandlerId}
    {concrete abstract : HandlerViolations} {req : Request}
    (hroute : RouteExtractionSound routes routeMap)
    (hhandlers : HandlerSound concrete abstract) :
    (frameworkAnalyzerRun routes routeMap concrete abstract req).Sound := by
  exact framework_route_sound hroute hhandlers req

/-! ## Demo using the triage theorem from NoBugHiding -/

def demoCIRun : AnalyzerRun :=
  { concrete := triageConcrete
  , abstract := triageAbstract
  }

def demoCITriage : TriageRun :=
  { report := triageReport
  , suppressed := triageSuppressed
  , evidence := [triageEvidence2]
  }

theorem demoCIRunSound : demoCIRun.Sound := triageSound

theorem demoCITriageComplete : demoCITriage.Complete demoCIRun := triageCompleteDemo

example : ListSubset demoCIRun.concrete demoCITriage.report :=
  ci_gate_no_bug_hiding demoCIRunSound demoCITriageComplete

example : 2 ∉ demoCIRun.concrete :=
  ci_gate_not_reported_not_concrete
    demoCIRunSound
    demoCITriageComplete
    (by simp [demoCITriage, triageReport])

end PcSastLean
