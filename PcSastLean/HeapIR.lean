import PcSastLean.SecurityIR

/-!
Heap/object-field extension.

Concrete execution has a single object target for each reference variable.
Abstract execution keeps a may-points-to set and over-approximates field writes
by joining the written taint into that field on every may-target object.
-/

namespace PcSastLean

abbrev Obj := Nat
abbrev Field := Nat

def joinLabels : List Label -> Label
  | [] => Label.clean
  | x :: xs => Label.join x (joinLabels xs)

theorem mem_le_joinLabels {x : Label} {xs : List Label}
    (h : x ∈ xs) :
    Label.le x (joinLabels xs) := by
  induction xs with
  | nil =>
      simp at h
  | cons y ys ih =>
      simp at h
      cases h with
      | inl hxy =>
          subst hxy
          exact Label.le_join_left x (joinLabels ys)
      | inr hy =>
          exact Label.le_trans (ih hy) (Label.le_join_right y (joinLabels ys))

structure ConcreteHeapState where
  vars : Var -> Label
  pointsTo : Var -> Obj
  heap : Obj -> Field -> Label

structure AbsHeapState where
  vars : Var -> Label
  pts : Var -> List Obj
  heap : Obj -> Field -> Label

structure HeapSound (c : ConcreteHeapState) (a : AbsHeapState) : Prop where
  varSound : forall v, Label.le (c.vars v) (a.vars v)
  ptsSound : forall v, c.pointsTo v ∈ a.pts v
  heapSound : forall o f, Label.le (c.heap o f) (a.heap o f)

def ConcreteHeapState.setVar (s : ConcreteHeapState) (v : Var) (l : Label) :
    ConcreteHeapState :=
  { s with vars := fun v' => if v' = v then l else s.vars v' }

def AbsHeapState.setVar (s : AbsHeapState) (v : Var) (l : Label) :
    AbsHeapState :=
  { s with vars := fun v' => if v' = v then l else s.vars v' }

def ConcreteHeapState.setField
    (s : ConcreteHeapState) (o : Obj) (f : Field) (l : Label) :
    ConcreteHeapState :=
  { s with heap := fun o' f' => if o' = o ∧ f' = f then l else s.heap o' f' }

def AbsHeapState.writeAllField
    (s : AbsHeapState) (f : Field) (l : Label) :
    AbsHeapState :=
  { s with heap := fun o f' => if f' = f then Label.join (s.heap o f') l else s.heap o f' }

def AbsHeapState.writeMayField
    (s : AbsHeapState) (base : Var) (f : Field) (l : Label) :
    AbsHeapState :=
  { s with heap := fun o f' =>
      if o ∈ s.pts base ∧ f' = f then Label.join (s.heap o f') l else s.heap o f' }

def readAbsField (s : AbsHeapState) (base : Var) (f : Field) : Label :=
  joinLabels ((s.pts base).map (fun o => s.heap o f))

theorem readAbsField_sound
    {c : ConcreteHeapState} {a : AbsHeapState}
    (hs : HeapSound c a) (base : Var) (f : Field) :
    Label.le (c.heap (c.pointsTo base) f) (readAbsField a base f) := by
  unfold readAbsField
  have hheap := hs.heapSound (c.pointsTo base) f
  have hmemObj := hs.ptsSound base
  have hmemLabel :
      a.heap (c.pointsTo base) f ∈ (a.pts base).map (fun o => a.heap o f) := by
    exact List.mem_map.mpr ⟨c.pointsTo base, hmemObj, rfl⟩
  exact Label.le_trans hheap (mem_le_joinLabels hmemLabel)

inductive HInstr where
  | source (dst : Var)
  | assign (dst src : Var)
  | sanitize (dst : Var)
  | storeField (base : Var) (field : Field) (src : Var)
  | loadField (dst : Var) (base : Var) (field : Field)
  | sink (src : Var) (id : Node)
deriving DecidableEq, Repr

structure HConcreteResult where
  state : ConcreteHeapState
  violation : Option Node

structure HAbsResult where
  state : AbsHeapState
  violation : Option Node

def optionViolation : Option Node -> List Node
  | none => []
  | some id => [id]

def stepConcreteHeap (s : ConcreteHeapState) : HInstr -> HConcreteResult
  | HInstr.source dst =>
      { state := s.setVar dst Label.tainted, violation := none }
  | HInstr.assign dst src =>
      { state := s.setVar dst (s.vars src), violation := none }
  | HInstr.sanitize dst =>
      { state := s.setVar dst Label.clean, violation := none }
  | HInstr.storeField base field src =>
      { state := s.setField (s.pointsTo base) field (s.vars src), violation := none }
  | HInstr.loadField dst base field =>
      { state := s.setVar dst (s.heap (s.pointsTo base) field), violation := none }
  | HInstr.sink src id =>
      { state := s, violation := if s.vars src = Label.tainted then some id else none }

def stepAbsHeap (s : AbsHeapState) : HInstr -> HAbsResult
  | HInstr.source dst =>
      { state := s.setVar dst Label.tainted, violation := none }
  | HInstr.assign dst src =>
      { state := s.setVar dst (s.vars src), violation := none }
  | HInstr.sanitize dst =>
      { state := s.setVar dst Label.clean, violation := none }
  | HInstr.storeField base field src =>
      { state := s.writeMayField base field (s.vars src), violation := none }
  | HInstr.loadField dst base field =>
      { state := s.setVar dst (readAbsField s base field), violation := none }
  | HInstr.sink src id =>
      { state := s, violation := if s.vars src = Label.tainted then some id else none }

theorem heap_setVar_sound
    {c : ConcreteHeapState} {a : AbsHeapState} {v : Var} {lc la : Label}
    (hs : HeapSound c a) (hl : Label.le lc la) :
    HeapSound (c.setVar v lc) (a.setVar v la) := by
  constructor
  · intro v'
    unfold ConcreteHeapState.setVar AbsHeapState.setVar
    by_cases h : v' = v
    · simp [h, hl]
    · simp [h, hs.varSound v']
  · intro v'
    exact hs.ptsSound v'
  · intro o f
    exact hs.heapSound o f

theorem heap_storeMayField_sound
    {c : ConcreteHeapState} {a : AbsHeapState}
    {base : Var} {field : Field} {src : Var}
    (hs : HeapSound c a) :
    HeapSound
      (c.setField (c.pointsTo base) field (c.vars src))
      (a.writeMayField base field (a.vars src)) := by
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
      have hpts := hs.ptsSound base
      simp [ConcreteHeapState.setField, AbsHeapState.writeMayField, hpts]
      exact Label.le_trans hsrc
        (Label.le_join_right (a.heap (c.pointsTo base) f) (a.vars src))
    · by_cases hf : f = field
      · subst hf
        have ho : o ≠ c.pointsTo base := by
          intro ho
          exact htarget ⟨ho, rfl⟩
        by_cases hpts : o ∈ a.pts base
        · simp [ConcreteHeapState.setField, AbsHeapState.writeMayField, ho, hpts]
          exact Label.le_trans (hs.heapSound o f)
            (Label.le_join_left (a.heap o f) (a.vars src))
        · simp [ConcreteHeapState.setField, AbsHeapState.writeMayField, ho, hpts, hs.heapSound o f]
      · simp [ConcreteHeapState.setField, AbsHeapState.writeMayField, hf, hs.heapSound o f]

theorem stepHeap_sound
    {c : ConcreteHeapState} {a : AbsHeapState} {i : HInstr}
    (hs : HeapSound c a) :
    HeapSound (stepConcreteHeap c i).state (stepAbsHeap a i).state /\
    ListSubset (optionViolation (stepConcreteHeap c i).violation)
      (optionViolation (stepAbsHeap a i).violation) := by
  cases i with
  | source dst =>
      constructor
      · exact heap_setVar_sound hs (Label.le_refl Label.tainted)
      · intro id hmem
        simp [stepConcreteHeap, stepAbsHeap, optionViolation] at hmem
  | assign dst src =>
      constructor
      · exact heap_setVar_sound hs (hs.varSound src)
      · intro id hmem
        simp [stepConcreteHeap, stepAbsHeap, optionViolation] at hmem
  | sanitize dst =>
      constructor
      · exact heap_setVar_sound hs (Label.le_refl Label.clean)
      · intro id hmem
        simp [stepConcreteHeap, stepAbsHeap, optionViolation] at hmem
  | storeField base field src =>
      constructor
      · exact heap_storeMayField_sound hs
      · intro id hmem
        simp [stepConcreteHeap, stepAbsHeap, optionViolation] at hmem
  | loadField dst base field =>
      constructor
      · exact heap_setVar_sound hs (readAbsField_sound hs base field)
      · intro id hmem
        simp [stepConcreteHeap, stepAbsHeap, optionViolation] at hmem
  | sink src sinkId =>
      constructor
      · exact hs
      · intro id hmem
        have hvar := hs.varSound src
        cases hc : c.vars src <;> cases ha : a.vars src
        · simp [stepConcreteHeap, stepAbsHeap, optionViolation, hc, ha] at hmem
        · simp [stepConcreteHeap, stepAbsHeap, optionViolation, hc, ha] at hmem
        · simp [Label.le, hc, ha] at hvar
        · simp [stepConcreteHeap, stepAbsHeap, optionViolation, hc, ha] at hmem ⊢
          exact hmem

def execConcreteHeap (s : ConcreteHeapState) : List HInstr -> ConcreteHeapState × List Node
  | [] => (s, [])
  | i :: rest =>
      let r := stepConcreteHeap s i
      let next := execConcreteHeap r.state rest
      (next.1, optionViolation r.violation ++ next.2)

def execAbsHeap (s : AbsHeapState) : List HInstr -> AbsHeapState × List Node
  | [] => (s, [])
  | i :: rest =>
      let r := stepAbsHeap s i
      let next := execAbsHeap r.state rest
      (next.1, optionViolation r.violation ++ next.2)

theorem execHeap_sound
    {c : ConcreteHeapState} {a : AbsHeapState} :
    forall prog : List HInstr,
      HeapSound c a ->
      HeapSound (execConcreteHeap c prog).1 (execAbsHeap a prog).1 /\
      ListSubset (execConcreteHeap c prog).2 (execAbsHeap a prog).2 := by
  intro prog
  induction prog generalizing c a with
  | nil =>
      intro hs
      constructor
      · exact hs
      · intro id hmem
        simp [execConcreteHeap] at hmem
  | cons i rest ih =>
      intro hs
      have hstep := stepHeap_sound (i := i) hs
      have htail := ih hstep.left
      constructor
      · simp [execConcreteHeap, execAbsHeap]
        exact htail.left
      · intro id hmem
        simp [execConcreteHeap, execAbsHeap] at hmem ⊢
        cases hmem with
        | inl hhead =>
            exact Or.inl (hstep.right id hhead)
        | inr hrest =>
            exact Or.inr (htail.right id hrest)

def SafeHeapProgram (s : AbsHeapState) (prog : List HInstr) : Prop :=
  forall id : Node, id ∉ (execAbsHeap s prog).2

theorem heap_abstract_safety_implies_concrete_safety
    {concrete : ConcreteHeapState} {abstract : AbsHeapState} {prog : List HInstr}
    (hs : HeapSound concrete abstract)
    (habs : SafeHeapProgram abstract prog) :
    forall id : Node, id ∉ (execConcreteHeap concrete prog).2 := by
  intro id hbad
  exact habs id ((execHeap_sound prog hs).right id hbad)

def demoConcreteHeap : ConcreteHeapState :=
  { vars := fun _ => Label.clean
  , pointsTo := fun _ => 0
  , heap := fun _ _ => Label.clean
  }

def demoAbsHeap : AbsHeapState :=
  { vars := fun _ => Label.clean
  , pts := fun _ => [0, 1]
  , heap := fun _ _ => Label.clean
  }

theorem demoHeapSound : HeapSound demoConcreteHeap demoAbsHeap := by
  constructor
  · intro _
    exact Label.le_refl Label.clean
  · intro _
    simp [demoConcreteHeap, demoAbsHeap]
  · intro _ _
    exact Label.le_refl Label.clean

def heapVulnerableProgram : List HInstr :=
  [ HInstr.source 0
  , HInstr.storeField 10 3 0
  , HInstr.loadField 1 10 3
  , HInstr.sink 1 17
  ]

example : (execConcreteHeap demoConcreteHeap heapVulnerableProgram).2 = [17] := by
  native_decide

example : (execAbsHeap demoAbsHeap heapVulnerableProgram).2 = [17] := by
  native_decide

example :
    ListSubset (execConcreteHeap demoConcreteHeap heapVulnerableProgram).2
      (execAbsHeap demoAbsHeap heapVulnerableProgram).2 :=
  (execHeap_sound heapVulnerableProgram demoHeapSound).right

def demoAbsHeapPrecise : AbsHeapState :=
  { vars := fun _ => Label.clean
  , pts := fun v => if v = 10 then [0] else [0, 1]
  , heap := fun _ _ => Label.clean
  }

theorem demoHeapPreciseSound : HeapSound demoConcreteHeap demoAbsHeapPrecise := by
  constructor
  · intro _
    exact Label.le_refl Label.clean
  · intro v
    by_cases h : v = 10
    · simp [demoConcreteHeap, demoAbsHeapPrecise, h]
    · simp [demoConcreteHeap, demoAbsHeapPrecise, h]
  · intro _ _
    exact Label.le_refl Label.clean

example :
    (stepAbsHeap demoAbsHeapPrecise (HInstr.storeField 10 3 0)).state.heap 1 3 =
      Label.clean := by
  native_decide

example :
    (execAbsHeap demoAbsHeapPrecise heapVulnerableProgram).2 = [17] := by
  native_decide

example :
    ListSubset (execConcreteHeap demoConcreteHeap heapVulnerableProgram).2
      (execAbsHeap demoAbsHeapPrecise heapVulnerableProgram).2 :=
  (execHeap_sound heapVulnerableProgram demoHeapPreciseSound).right

end PcSastLean
