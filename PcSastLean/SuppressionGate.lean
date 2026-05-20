import PcSastLean.SanitizerLattice

/-!
Verified suppression gates.

SAST teams suppress findings all the time: infeasible path, unreachable route,
framework guard, test-only sink, dead feature flag, and so on.  The dangerous
version is a comment-only suppression that also hides a real concrete bug.

This module makes suppression proof-carrying.  A suppressed finding is accepted
only if an obligation proves that the corresponding concrete violation cannot
occur.  Then the reported findings still cover every concrete violation.
-/

namespace PcSastLean

def SoundSuppression (concrete suppressed : List Node) : Prop :=
  forall id, id ∈ suppressed -> id ∉ concrete

def ReportCoversUnsuppressed
    (abstract report suppressed : List Node) : Prop :=
  forall id, id ∈ abstract -> id ∈ report ∨ id ∈ suppressed

theorem suppression_gate
    {concrete abstract report suppressed : List Node}
    (hsound : ListSubset concrete abstract)
    (hcover : ReportCoversUnsuppressed abstract report suppressed)
    (hsupp : SoundSuppression concrete suppressed) :
    ListSubset concrete report := by
  intro id hconcrete
  have habstract := hsound id hconcrete
  cases hcover id habstract with
  | inl hreport =>
      exact hreport
  | inr hsuppressed =>
      exact False.elim ((hsupp id hsuppressed) hconcrete)

theorem not_reported_not_concrete
    {concrete abstract report suppressed : List Node} {sink : Node}
    (hsound : ListSubset concrete abstract)
    (hcover : ReportCoversUnsuppressed abstract report suppressed)
    (hsupp : SoundSuppression concrete suppressed)
    (hnotReport : sink ∉ report) :
    sink ∉ concrete := by
  intro hconcrete
  exact hnotReport (suppression_gate hsound hcover hsupp sink hconcrete)

theorem heap_suppression_gate
    {concrete : ConcreteHeapState} {abstract : AbsHeapState}
    {prog : List HInstr} {report suppressed : List Node}
    (hs : HeapSound concrete abstract)
    (hcover : ReportCoversUnsuppressed (execAbsHeap abstract prog).2 report suppressed)
    (hsupp : SoundSuppression (execConcreteHeap concrete prog).2 suppressed) :
    ListSubset (execConcreteHeap concrete prog).2 report := by
  exact suppression_gate (execHeap_sound prog hs).right hcover hsupp

theorem sanitizer_suppression_gate
    {concrete abstract : SecStore}
    {prog : List SInstr} {report suppressed : List Node}
    (hs : SecStore.Sound concrete abstract)
    (hcover : ReportCoversUnsuppressed (sexec abstract prog).2 report suppressed)
    (hsupp : SoundSuppression (sexec concrete prog).2 suppressed) :
    ListSubset (sexec concrete prog).2 report := by
  exact suppression_gate (sexec_sound prog hs).right hcover hsupp

/-! ## Heap false-positive demo -/

def aliasConcreteHeap : ConcreteHeapState :=
  { vars := fun _ => Label.clean
  , pointsTo := fun v => if v = 20 then 1 else 0
  , heap := fun _ _ => Label.clean
  }

def aliasAbstractHeap : AbsHeapState :=
  { vars := fun _ => Label.clean
  , pts := fun v => if v = 10 then [0] else if v = 20 then [0, 1] else [0]
  , heap := fun _ _ => Label.clean
  }

theorem aliasHeapSound : HeapSound aliasConcreteHeap aliasAbstractHeap := by
  constructor
  · intro _
    exact Label.le_refl Label.clean
  · intro v
    by_cases h20 : v = 20
    · simp [aliasConcreteHeap, aliasAbstractHeap, h20]
    · by_cases h10 : v = 10
      · simp [aliasConcreteHeap, aliasAbstractHeap, h20, h10]
      · simp [aliasConcreteHeap, aliasAbstractHeap, h20, h10]
  · intro _ _
    exact Label.le_refl Label.clean

def aliasFalsePositiveProgram : List HInstr :=
  [ HInstr.source 0
  , HInstr.storeField 10 3 0
  , HInstr.loadField 1 20 3
  , HInstr.sink 1 41
  ]

example : (execConcreteHeap aliasConcreteHeap aliasFalsePositiveProgram).2 = [] := by
  native_decide

example : (execAbsHeap aliasAbstractHeap aliasFalsePositiveProgram).2 = [41] := by
  native_decide

def aliasSuppressed : List Node := [41]

example :
    SoundSuppression
      (execConcreteHeap aliasConcreteHeap aliasFalsePositiveProgram).2
      aliasSuppressed := by
  intro id _hsup hconcrete
  have hrun : (execConcreteHeap aliasConcreteHeap aliasFalsePositiveProgram).2 = [] := by
    native_decide
  rw [hrun] at hconcrete
  simp at hconcrete

example :
    ListSubset
      (execConcreteHeap aliasConcreteHeap aliasFalsePositiveProgram).2
      [] :=
  heap_suppression_gate
    aliasHeapSound
    (report := [])
    (suppressed := aliasSuppressed)
    (by
      intro id habs
      right
      have hrun : (execAbsHeap aliasAbstractHeap aliasFalsePositiveProgram).2 = [41] := by
        native_decide
      rw [hrun] at habs
      simp [aliasSuppressed] at habs ⊢
      exact habs)
    (by
      intro id _hsup hconcrete
      have hrun : (execConcreteHeap aliasConcreteHeap aliasFalsePositiveProgram).2 = [] := by
        native_decide
      rw [hrun] at hconcrete
      simp at hconcrete)

end PcSastLean
