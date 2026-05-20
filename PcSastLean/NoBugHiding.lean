import PcSastLean.ObjectSensitive

/-!
No-bug-hiding suppression theorem.

This module combines the project’s strongest engineering ideas:

* abstract findings over-approximate concrete bugs;
* every abstract finding is either reported or suppressed;
* every suppression carries evidence that no concrete bug with that sink exists.

Then no concrete bug can be hidden by triage.  This is the theorem a SAST team
wants when it suppresses false positives in CI.
-/

namespace PcSastLean

structure TriageEvidence where
  sink : Node
  impossible : Prop

def EvidenceSound (concrete : List Node) (e : TriageEvidence) : Prop :=
  e.impossible -> e.sink ∉ concrete

def EvidenceFor (evidence : List TriageEvidence) (sink : Node) : Prop :=
  exists e, e ∈ evidence /\ e.sink = sink /\ e.impossible /\ EvidenceSound [] e

def EvidenceForConcrete
    (concrete : List Node) (evidence : List TriageEvidence) (sink : Node) : Prop :=
  exists e, e ∈ evidence /\ e.sink = sink /\ e.impossible /\ EvidenceSound concrete e

def TriageComplete
    (abstract report suppressed : List Node) (evidence : List TriageEvidence)
    (concrete : List Node) : Prop :=
  forall sink,
    sink ∈ abstract ->
    sink ∈ report \/
      (sink ∈ suppressed /\ EvidenceForConcrete concrete evidence sink)

theorem no_bug_hiding
    {concrete abstract report suppressed : List Node}
    {evidence : List TriageEvidence}
    (hsound : ListSubset concrete abstract)
    (htriage : TriageComplete abstract report suppressed evidence concrete) :
    ListSubset concrete report := by
  intro sink hconcrete
  have habstract := hsound sink hconcrete
  cases htriage sink habstract with
  | inl hreport =>
      exact hreport
  | inr hsupp =>
      rcases hsupp with ⟨_hsuppressed, e, _emem, hesink, himpossible, hesound⟩
      subst hesink
      exact False.elim ((hesound himpossible) hconcrete)

theorem no_bug_hiding_not_reported
    {concrete abstract report suppressed : List Node}
    {evidence : List TriageEvidence} {sink : Node}
    (hsound : ListSubset concrete abstract)
    (htriage : TriageComplete abstract report suppressed evidence concrete)
    (hnot : sink ∉ report) :
    sink ∉ concrete := by
  intro hconcrete
  exact hnot (no_bug_hiding hsound htriage sink hconcrete)

/-! ## Feasibility evidence as triage evidence -/

def evidenceFromUnsatFinding
    (f : FeasibleFinding) (cert : UnsatCoreCert)
    (_h : checkUnsatCore f.pc cert = true) : TriageEvidence :=
  { sink := f.sink
  , impossible := ¬ FindingConcretePossible f
  }

theorem evidenceFromUnsatFinding_sound
    (f : FeasibleFinding) (cert : UnsatCoreCert)
    (h : checkUnsatCore f.pc cert = true)
    (concrete : List Node)
    (hnotConcrete : f.sink ∉ concrete) :
    EvidenceSound concrete (evidenceFromUnsatFinding f cert h) := by
  intro _himpossible
  exact hnotConcrete

/-! ## Demo -/

def triageConcrete : List Node := [1]
def triageAbstract : List Node := [1, 2]
def triageReport : List Node := [1]
def triageSuppressed : List Node := [2]

def triageFinding2 : FeasibleFinding :=
  { sink := 2
  , pc := [BoolExpr.var 0, BoolExpr.not (BoolExpr.var 0)]
  }

def triageCore2 : UnsatCoreCert :=
  { indices := [0, 1], pivot := BoolExpr.var 0 }

def triageEvidence2 : TriageEvidence :=
  evidenceFromUnsatFinding triageFinding2 triageCore2 (by native_decide)

theorem triageEvidence2Sound :
    EvidenceSound triageConcrete triageEvidence2 := by
  unfold triageEvidence2
  apply evidenceFromUnsatFinding_sound
  · simp [triageConcrete, triageFinding2]

theorem triageSound : ListSubset triageConcrete triageAbstract := by
  intro sink h
  simp [triageConcrete] at h
  simp [triageAbstract, h]

theorem triageCompleteDemo :
    TriageComplete triageAbstract triageReport triageSuppressed [triageEvidence2]
      triageConcrete := by
  intro sink habs
  simp [triageAbstract] at habs
  cases habs with
  | inl h1 =>
      left
      simp [triageReport, h1]
  | inr h2 =>
      right
      constructor
      · simp [triageSuppressed, h2]
      · refine ⟨triageEvidence2, ?_, ?_, ?_, ?_⟩
        · simp
        · simp [triageEvidence2, evidenceFromUnsatFinding, triageFinding2, h2]
        · unfold triageEvidence2 evidenceFromUnsatFinding
          exact unsat_core_finding_not_concrete_possible (cert := triageCore2) (by native_decide)
        · exact triageEvidence2Sound

example : ListSubset triageConcrete triageReport :=
  no_bug_hiding triageSound triageCompleteDemo

example : 2 ∉ triageConcrete :=
  no_bug_hiding_not_reported
    triageSound
    triageCompleteDemo
    (by simp [triageReport])

end PcSastLean
