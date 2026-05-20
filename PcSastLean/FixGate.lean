import PcSastLean.BaselineGate

/-!
Verified fix gates.

Baseline gates prove "no new finding outside the accepted set".  Fix gates are
more pointed: they prove that a specific vulnerability sink cannot still occur in
concrete execution after a patch, as long as the sound abstract run no longer
contains that sink.

This is the theorem a security-fix PR wants:

  "The patched abstract analysis excludes CWE sink S, therefore the patched
   concrete execution excludes S."
-/

namespace PcSastLean

def SinkRemoved (sink : Node) (violations : List Node) : Prop :=
  sink ∉ violations

theorem fix_gate_linear
    {concrete abstract : Store} {patched : List Instr} {sink : Node}
    (hs : Store.le concrete abstract)
    (habs : SinkRemoved sink (exec abstract patched).2) :
    SinkRemoved sink (exec concrete patched).2 := by
  intro hbad
  exact habs ((exec_sound patched hs).right sink hbad)

theorem fix_gate_blocks
    {concrete abstract : Store} {patched : List Block} {sink : Node}
    (hall : forall b, b ∈ patched -> BlockSound b)
    (hs : Store.le concrete abstract)
    (habs : SinkRemoved sink (execAbstractBlocks abstract patched).2) :
    SinkRemoved sink (execConcreteBlocks concrete patched).2 := by
  intro hbad
  exact habs ((blocks_sound patched hall hs).right sink hbad)

theorem fix_gate_heap
    {concrete : ConcreteHeapState} {abstract : AbsHeapState}
    {patched : List HInstr} {sink : Node}
    (hs : HeapSound concrete abstract)
    (habs : SinkRemoved sink (execAbsHeap abstract patched).2) :
    SinkRemoved sink (execConcreteHeap concrete patched).2 := by
  intro hbad
  exact habs ((execHeap_sound patched hs).right sink hbad)

theorem regression_fix_gate_heap
    {concrete : ConcreteHeapState} {abstract : AbsHeapState}
    {old patched : List HInstr} {sink : Node}
    (hs : HeapSound concrete abstract)
    (oldHadSink : sink ∈ (execAbsHeap abstract old).2)
    (patchedRemovedSink : SinkRemoved sink (execAbsHeap abstract patched).2) :
    sink ∈ (execAbsHeap abstract old).2 /\
    SinkRemoved sink (execConcreteHeap concrete patched).2 := by
  exact And.intro oldHadSink (fix_gate_heap hs patchedRemovedSink)

/-! ## Demos -/

def heapPatchedProgram : List HInstr :=
  [ HInstr.source 0
  , HInstr.sanitize 2
  , HInstr.storeField 10 3 2
  , HInstr.loadField 1 10 3
  , HInstr.sink 1 17
  ]

example : 17 ∈ (execAbsHeap demoAbsHeapPrecise heapVulnerableProgram).2 := by
  native_decide

example : SinkRemoved 17 (execAbsHeap demoAbsHeapPrecise heapPatchedProgram).2 := by
  unfold SinkRemoved
  native_decide

example : SinkRemoved 17 (execConcreteHeap demoConcreteHeap heapPatchedProgram).2 :=
  fix_gate_heap
    demoHeapPreciseSound
    (by
      unfold SinkRemoved
      native_decide)

example :
    17 ∈ (execAbsHeap demoAbsHeapPrecise heapVulnerableProgram).2 /\
    SinkRemoved 17 (execConcreteHeap demoConcreteHeap heapPatchedProgram).2 :=
  regression_fix_gate_heap
    demoHeapPreciseSound
    (old := heapVulnerableProgram)
    (patched := heapPatchedProgram)
    (sink := 17)
    (by native_decide)
    (by
      unfold SinkRemoved
      native_decide)

end PcSastLean
