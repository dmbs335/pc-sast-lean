import PcSastLean.MiniSourceCallback

/-!
Pointer arithmetic and offset-sensitive aliasing.

The heap modules model object fields and allocation sites, but not arithmetic on
pointers.  This module adds a small offset-pointer abstraction.  Concrete
execution has one exact pointer per variable.  Abstract execution keeps a set of
possible base+offset pointers and over-approximates reads/writes by joining over
that may-set.

Claim boundary:

* Verified here: pointer addition, may-pointer reads, and may-pointer writes
  preserve soundness in a finite base+offset pointer model.
* External obligations: production frontends must justify how real pointer
  arithmetic, arrays, slices, unsafe casts, and native memory map into this
  model.
* Not modeled here: undefined behavior, negative offsets, byte-level layout,
  pointer provenance rules, concurrency, or C/C++ aliasing standards.
-/

namespace PcSastLean

abbrev PtrBase := Nat
abbrev PtrOffset := Nat

structure OffsetPtr where
  base : PtrBase
  offset : PtrOffset
deriving DecidableEq, Repr

def OffsetPtr.add (p : OffsetPtr) (delta : PtrOffset) : OffsetPtr :=
  { base := p.base, offset := p.offset + delta }

structure ConcreteOffsetHeap where
  vars : Var -> Label
  pointsTo : Var -> OffsetPtr
  mem : OffsetPtr -> Label

structure AbsOffsetHeap where
  vars : Var -> Label
  ptrs : Var -> List OffsetPtr
  mem : OffsetPtr -> Label

structure OffsetHeapSound (c : ConcreteOffsetHeap) (a : AbsOffsetHeap) : Prop where
  varSound : forall v, Label.le (c.vars v) (a.vars v)
  ptrSound : forall v, c.pointsTo v ∈ a.ptrs v
  memSound : forall p, Label.le (c.mem p) (a.mem p)

def ConcreteOffsetHeap.setVar
    (s : ConcreteOffsetHeap) (v : Var) (l : Label) : ConcreteOffsetHeap :=
  { s with vars := fun v' => if v' = v then l else s.vars v' }

def AbsOffsetHeap.setVar
    (s : AbsOffsetHeap) (v : Var) (l : Label) : AbsOffsetHeap :=
  { s with vars := fun v' => if v' = v then l else s.vars v' }

def ConcreteOffsetHeap.setPtr
    (s : ConcreteOffsetHeap) (v : Var) (p : OffsetPtr) : ConcreteOffsetHeap :=
  { s with pointsTo := fun v' => if v' = v then p else s.pointsTo v' }

def AbsOffsetHeap.setPtrs
    (s : AbsOffsetHeap) (v : Var) (ps : List OffsetPtr) : AbsOffsetHeap :=
  { s with ptrs := fun v' => if v' = v then ps else s.ptrs v' }

def ConcreteOffsetHeap.setMem
    (s : ConcreteOffsetHeap) (p : OffsetPtr) (l : Label) : ConcreteOffsetHeap :=
  { s with mem := fun p' => if p' = p then l else s.mem p' }

def AbsOffsetHeap.writeMayPtr
    (s : AbsOffsetHeap) (base : Var) (l : Label) : AbsOffsetHeap :=
  { s with mem := fun p =>
      if p ∈ s.ptrs base then Label.join (s.mem p) l else s.mem p }

def readAbsPtr (s : AbsOffsetHeap) (base : Var) : Label :=
  joinLabels ((s.ptrs base).map (fun p => s.mem p))

theorem offset_setVar_sound
    {c : ConcreteOffsetHeap} {a : AbsOffsetHeap} {v : Var} {lc la : Label}
    (hs : OffsetHeapSound c a) (hl : Label.le lc la) :
    OffsetHeapSound (c.setVar v lc) (a.setVar v la) := by
  constructor
  · intro v'
    unfold ConcreteOffsetHeap.setVar AbsOffsetHeap.setVar
    by_cases h : v' = v
    · simp [h, hl]
    · simp [h, hs.varSound v']
  · intro v'
    exact hs.ptrSound v'
  · intro p
    exact hs.memSound p

theorem offset_ptr_add_sound
    {c : ConcreteOffsetHeap} {a : AbsOffsetHeap}
    {dst src : Var} {delta : PtrOffset}
    (hs : OffsetHeapSound c a) :
    OffsetHeapSound
      (c.setPtr dst ((c.pointsTo src).add delta))
      (a.setPtrs dst ((a.ptrs src).map (fun p => p.add delta))) := by
  constructor
  · intro v
    exact hs.varSound v
  · intro v
    unfold ConcreteOffsetHeap.setPtr AbsOffsetHeap.setPtrs
    by_cases h : v = dst
    · simp [h]
      exact ⟨c.pointsTo src, hs.ptrSound src, rfl⟩
    · simp [h, hs.ptrSound v]
  · intro p
    exact hs.memSound p

theorem readAbsPtr_sound
    {c : ConcreteOffsetHeap} {a : AbsOffsetHeap}
    (hs : OffsetHeapSound c a) (base : Var) :
    Label.le (c.mem (c.pointsTo base)) (readAbsPtr a base) := by
  unfold readAbsPtr
  have hmemSound := hs.memSound (c.pointsTo base)
  have hptr := hs.ptrSound base
  have hmem :
      a.mem (c.pointsTo base) ∈ (a.ptrs base).map (fun p => a.mem p) := by
    exact List.mem_map.mpr ⟨c.pointsTo base, hptr, rfl⟩
  exact Label.le_trans hmemSound (mem_le_joinLabels hmem)

theorem offset_writeMayPtr_sound
    {c : ConcreteOffsetHeap} {a : AbsOffsetHeap}
    {base src : Var}
    (hs : OffsetHeapSound c a) :
    OffsetHeapSound
      (c.setMem (c.pointsTo base) (c.vars src))
      (a.writeMayPtr base (a.vars src)) := by
  constructor
  · intro v
    exact hs.varSound v
  · intro v
    exact hs.ptrSound v
  · intro p
    by_cases htarget : p = c.pointsTo base
    · subst htarget
      have hptr := hs.ptrSound base
      have hsrc := hs.varSound src
      simp [ConcreteOffsetHeap.setMem, AbsOffsetHeap.writeMayPtr, hptr]
      exact Label.le_trans hsrc
        (Label.le_join_right (a.mem (c.pointsTo base)) (a.vars src))
    · by_cases hmay : p ∈ a.ptrs base
      · simp [ConcreteOffsetHeap.setMem, AbsOffsetHeap.writeMayPtr, htarget, hmay]
        exact Label.le_trans (hs.memSound p)
          (Label.le_join_left (a.mem p) (a.vars src))
      · simp [ConcreteOffsetHeap.setMem, AbsOffsetHeap.writeMayPtr, htarget, hmay,
          hs.memSound p]

theorem offset_load_sound
    {c : ConcreteOffsetHeap} {a : AbsOffsetHeap}
    {dst base : Var}
    (hs : OffsetHeapSound c a) :
    OffsetHeapSound
      (c.setVar dst (c.mem (c.pointsTo base)))
      (a.setVar dst (readAbsPtr a base)) := by
  exact offset_setVar_sound hs (readAbsPtr_sound hs base)

/-! ## Demo -/

def offsetPtr0 : OffsetPtr := { base := 0, offset := 0 }
def offsetPtr4 : OffsetPtr := { base := 0, offset := 4 }

def offsetConcrete : ConcreteOffsetHeap :=
  { vars := fun v => if v = 1 then Label.tainted else Label.clean
  , pointsTo := fun _ => offsetPtr0
  , mem := fun _ => Label.clean
  }

def offsetAbstract : AbsOffsetHeap :=
  { vars := fun v => if v = 1 then Label.tainted else Label.clean
  , ptrs := fun _ => [offsetPtr0]
  , mem := fun _ => Label.clean
  }

theorem offsetDemoSound : OffsetHeapSound offsetConcrete offsetAbstract := by
  constructor
  · intro v
    by_cases h : v = 1
    · simp [offsetConcrete, offsetAbstract, h, Label.le_refl]
    · simp [offsetConcrete, offsetAbstract, h, Label.le_refl]
  · intro _
    simp [offsetConcrete, offsetAbstract, offsetPtr0]
  · intro _
    exact Label.le_refl Label.clean

example :
    OffsetHeapSound
      (offsetConcrete.setPtr 2 (offsetPtr0.add 4))
      (offsetAbstract.setPtrs 2 ((offsetAbstract.ptrs 0).map (fun p => p.add 4))) :=
  offset_ptr_add_sound (dst := 2) (src := 0) (delta := 4) offsetDemoSound

example :
    OffsetHeapSound
      ((offsetConcrete.setPtr 2 (offsetPtr0.add 4)).setMem offsetPtr4 Label.tainted)
      ((offsetAbstract.setPtrs 2 [offsetPtr4]).writeMayPtr 2 Label.tainted) := by
  have hsAdd :
      OffsetHeapSound
        (offsetConcrete.setPtr 2 (offsetPtr0.add 4))
        (offsetAbstract.setPtrs 2 [offsetPtr4]) := by
    simpa [offsetConcrete, offsetAbstract, offsetPtr0, offsetPtr4, OffsetPtr.add] using
      (offset_ptr_add_sound (dst := 2) (src := 0) (delta := 4) offsetDemoSound)
  simpa [offsetConcrete, offsetPtr0, offsetPtr4, OffsetPtr.add] using
    (offset_writeMayPtr_sound (base := 2) (src := 1) hsAdd)

end PcSastLean
