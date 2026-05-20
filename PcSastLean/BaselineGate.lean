import PcSastLean.HeapIR

/-!
Verified baseline gates.

The usual formal-methods statement is "abstract no-bad implies concrete no-bad".
That is clean, but not how most SAST rollouts work.  Real projects often have a
large accepted baseline and want a CI gate that proves: this change introduced no
new concrete vulnerability outside the approved baseline.

This file captures that engineering theorem for the linear IR, block/call IR,
and heap IR.
-/

namespace PcSastLean

def CoveredByBaseline (violations baseline : List Node) : Prop :=
  ListSubset violations baseline

def NoNewConcreteViolations
    (concreteViolations baseline : List Node) : Prop :=
  ListSubset concreteViolations baseline

theorem baseline_gate_linear
    {concrete abstract : Store} {prog : List Instr} {baseline : List Node}
    (hs : Store.le concrete abstract)
    (habs : CoveredByBaseline (exec abstract prog).2 baseline) :
    NoNewConcreteViolations (exec concrete prog).2 baseline := by
  exact ListSubset.trans (exec_sound prog hs).right habs

theorem baseline_gate_blocks
    {concrete abstract : Store} {blocks : List Block} {baseline : List Node}
    (hall : forall b, b ∈ blocks -> BlockSound b)
    (hs : Store.le concrete abstract)
    (habs : CoveredByBaseline (execAbstractBlocks abstract blocks).2 baseline) :
    NoNewConcreteViolations (execConcreteBlocks concrete blocks).2 baseline := by
  exact ListSubset.trans (blocks_sound blocks hall hs).right habs

theorem baseline_gate_heap
    {concrete : ConcreteHeapState} {abstract : AbsHeapState}
    {prog : List HInstr} {baseline : List Node}
    (hs : HeapSound concrete abstract)
    (habs : CoveredByBaseline (execAbsHeap abstract prog).2 baseline) :
    NoNewConcreteViolations (execConcreteHeap concrete prog).2 baseline := by
  exact ListSubset.trans (execHeap_sound prog hs).right habs

theorem sink_absence_from_baseline_linear
    {concrete abstract : Store} {prog : List Instr} {baseline : List Node} {sink : Node}
    (hs : Store.le concrete abstract)
    (habs : CoveredByBaseline (exec abstract prog).2 baseline)
    (hnot : sink ∉ baseline) :
    sink ∉ (exec concrete prog).2 := by
  intro hbad
  exact hnot (baseline_gate_linear hs habs sink hbad)

theorem sink_absence_from_baseline_heap
    {concrete : ConcreteHeapState} {abstract : AbsHeapState}
    {prog : List HInstr} {baseline : List Node} {sink : Node}
    (hs : HeapSound concrete abstract)
    (habs : CoveredByBaseline (execAbsHeap abstract prog).2 baseline)
    (hnot : sink ∉ baseline) :
    sink ∉ (execConcreteHeap concrete prog).2 := by
  intro hbad
  exact hnot (baseline_gate_heap hs habs sink hbad)

/-! ## Demos -/

def approvedBaseline : List Node := [17]

example :
    CoveredByBaseline (execAbsHeap demoAbsHeapPrecise heapVulnerableProgram).2
      approvedBaseline := by
  have hrun : (execAbsHeap demoAbsHeapPrecise heapVulnerableProgram).2 = [17] := by
    native_decide
  intro id hmem
  rw [hrun] at hmem
  simp [approvedBaseline] at hmem ⊢
  exact hmem

example :
    NoNewConcreteViolations
      (execConcreteHeap demoConcreteHeap heapVulnerableProgram).2
      approvedBaseline :=
  baseline_gate_heap
    demoHeapPreciseSound
    (by
      have hrun : (execAbsHeap demoAbsHeapPrecise heapVulnerableProgram).2 = [17] := by
        native_decide
      intro id hmem
      rw [hrun] at hmem
      simp [approvedBaseline] at hmem ⊢
      exact hmem)

example :
    99 ∉ (execConcreteHeap demoConcreteHeap heapVulnerableProgram).2 :=
  sink_absence_from_baseline_heap
    demoHeapPreciseSound
    (baseline := approvedBaseline)
    (by
      have hrun : (execAbsHeap demoAbsHeapPrecise heapVulnerableProgram).2 = [17] := by
        native_decide
      intro id hmem
      rw [hrun] at hmem
      simp [approvedBaseline] at hmem ⊢
      exact hmem)
    (by simp [approvedBaseline])

end PcSastLean
