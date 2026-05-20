import PcSastLean.ORM

/-!
Allocation-site abstraction.

HeapIR used explicit may-points-to object sets.  Many practical pointer analyses
collapse concrete objects by allocation site.  This module verifies the core
soundness obligation for that abstraction: if a concrete object belongs to an
allocation site in the abstract points-to set, reads and writes through that
abstract site heap over-approximate the concrete object heap.
-/

namespace PcSastLean

abbrev AllocSite := Nat

structure ConcreteAllocHeap where
  vars : Var -> Label
  pointsTo : Var -> Obj
  siteOf : Obj -> AllocSite
  heap : Obj -> Field -> Label

structure AbsAllocHeap where
  vars : Var -> Label
  pts : Var -> List AllocSite
  heap : AllocSite -> Field -> Label

structure AllocHeapSound (c : ConcreteAllocHeap) (a : AbsAllocHeap) : Prop where
  varSound : forall v, Label.le (c.vars v) (a.vars v)
  ptsSound : forall v, c.siteOf (c.pointsTo v) ∈ a.pts v
  heapSound : forall o f, Label.le (c.heap o f) (a.heap (c.siteOf o) f)

def readAbsAllocField (s : AbsAllocHeap) (base : Var) (f : Field) : Label :=
  joinLabels ((s.pts base).map (fun site => s.heap site f))

theorem readAbsAllocField_sound
    {c : ConcreteAllocHeap} {a : AbsAllocHeap}
    (hs : AllocHeapSound c a) (base : Var) (f : Field) :
    Label.le (c.heap (c.pointsTo base) f) (readAbsAllocField a base f) := by
  unfold readAbsAllocField
  have hheap := hs.heapSound (c.pointsTo base) f
  have hsite := hs.ptsSound base
  have hmem :
      a.heap (c.siteOf (c.pointsTo base)) f ∈
        (a.pts base).map (fun site => a.heap site f) := by
    exact List.mem_map.mpr ⟨c.siteOf (c.pointsTo base), hsite, rfl⟩
  exact Label.le_trans hheap (mem_le_joinLabels hmem)

def ConcreteAllocHeap.setField
    (s : ConcreteAllocHeap) (o : Obj) (f : Field) (l : Label) :
    ConcreteAllocHeap :=
  { s with heap := fun o' f' => if o' = o ∧ f' = f then l else s.heap o' f' }

def AbsAllocHeap.writeMaySiteField
    (s : AbsAllocHeap) (base : Var) (f : Field) (l : Label) :
    AbsAllocHeap :=
  { s with heap := fun site f' =>
      if site ∈ s.pts base ∧ f' = f then Label.join (s.heap site f') l else s.heap site f' }

theorem alloc_writeMayField_sound
    {c : ConcreteAllocHeap} {a : AbsAllocHeap}
    {base : Var} {field : Field} {src : Var}
    (hs : AllocHeapSound c a) :
    AllocHeapSound
      (c.setField (c.pointsTo base) field (c.vars src))
      (a.writeMaySiteField base field (a.vars src)) := by
  constructor
  · intro v
    exact hs.varSound v
  · intro v
    exact hs.ptsSound v
  · intro o f
    by_cases htarget : o = c.pointsTo base ∧ f = field
    · rcases htarget with ⟨ho, hf⟩
      subst ho
      subst hf
      have hsrc := hs.varSound src
      have hsite := hs.ptsSound base
      simp [ConcreteAllocHeap.setField, AbsAllocHeap.writeMaySiteField, hsite]
      exact Label.le_trans hsrc
        (Label.le_join_right (a.heap (c.siteOf (c.pointsTo base)) f) (a.vars src))
    · by_cases hf : f = field
      · subst hf
        by_cases hsite : c.siteOf o ∈ a.pts base
        · by_cases ho : o = c.pointsTo base
          · exact False.elim (htarget ⟨ho, rfl⟩)
          · simp [ConcreteAllocHeap.setField, AbsAllocHeap.writeMaySiteField, ho, hsite]
            exact Label.le_trans (hs.heapSound o f)
              (Label.le_join_left (a.heap (c.siteOf o) f) (a.vars src))
        · have hnotObj : o ≠ c.pointsTo base := by
            intro ho
            subst ho
            exact hsite (hs.ptsSound base)
          simp [ConcreteAllocHeap.setField, AbsAllocHeap.writeMaySiteField, hnotObj, hsite,
            hs.heapSound o f]
      · simp [ConcreteAllocHeap.setField, AbsAllocHeap.writeMaySiteField, hf, hs.heapSound o f]

/-! ## Demo -/

def allocConcrete : ConcreteAllocHeap :=
  { vars := fun v => if v = 1 then Label.tainted else Label.clean
  , pointsTo := fun _ => 100
  , siteOf := fun _ => 7
  , heap := fun _ _ => Label.clean
  }

def allocAbstract : AbsAllocHeap :=
  { vars := fun v => if v = 1 then Label.tainted else Label.clean
  , pts := fun _ => [7]
  , heap := fun _ _ => Label.clean
  }

theorem allocDemoSound : AllocHeapSound allocConcrete allocAbstract := by
  constructor
  · intro v
    by_cases h : v = 1
    · simp [allocConcrete, allocAbstract, h, Label.le_refl]
    · simp [allocConcrete, allocAbstract, h, Label.le_refl]
  · intro _
    simp [allocConcrete, allocAbstract]
  · intro _ _
    exact Label.le_refl Label.clean

example :
    Label.le
      (allocConcrete.heap (allocConcrete.pointsTo 0) 3)
      (readAbsAllocField allocAbstract 0 3) :=
  readAbsAllocField_sound allocDemoSound 0 3

example :
    AllocHeapSound
      (allocConcrete.setField (allocConcrete.pointsTo 0) 3 Label.tainted)
      (allocAbstract.writeMaySiteField 0 3 Label.tainted) :=
  alloc_writeMayField_sound (base := 0) (field := 3) (src := 1) allocDemoSound

end PcSastLean
