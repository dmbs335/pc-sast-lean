import PcSastLean.AllocationSite

/-!
Object-sensitive allocation-site keys.

Allocation-site abstraction can merge too much.  Object-sensitive analyses refine
an allocation site by a context key, often derived from the receiver object or a
call string.  This module shows the basic relation: a context-sensitive heap can
be projected to a context-insensitive heap by joining over contexts, and any
object-sensitive sound heap is also sound after projection.

Claim boundary:

* Verified here: if an object-sensitive heap abstraction is sound, projecting by
  joining over context keys yields a sound allocation-site abstraction.
* External obligations: an analyzer must justify the meaning and construction of
  context keys.
* Not modeled here: real call-string-k construction, receiver-type sensitivity,
  virtual dispatch precision, or alias precision claims.
-/

namespace PcSastLean

abbrev ContextKey := Nat

structure ObjSensKey where
  site : AllocSite
  ctx : ContextKey
deriving DecidableEq, Repr

structure AbsObjSensHeap where
  vars : Var -> Label
  pts : Var -> List ObjSensKey
  heap : ObjSensKey -> Field -> Label

structure ObjSensHeapSound (c : ConcreteAllocHeap) (a : AbsObjSensHeap) : Prop where
  varSound : forall v, Label.le (c.vars v) (a.vars v)
  ptsSound : forall v, exists key, key ∈ a.pts v /\ key.site = c.siteOf (c.pointsTo v)
  heapSound : forall o f key,
    key.site = c.siteOf o ->
    key ∈ a.pts 0 \/ True ->
    Label.le (c.heap o f) (a.heap key f)

def keysForSite (keys : List ObjSensKey) (site : AllocSite) : List ObjSensKey :=
  keys.filter (fun k => decide (k.site = site))

def joinKeyHeap (a : AbsObjSensHeap) (keys : List ObjSensKey) (f : Field) : Label :=
  joinLabels (keys.map (fun k => a.heap k f))

def projectObjSensHeap (a : AbsObjSensHeap) : AbsAllocHeap :=
  { vars := a.vars
  , pts := fun v => (a.pts v).map (fun k => k.site)
  , heap := fun site f => joinKeyHeap a (keysForSite (a.pts 0) site) f
  }

theorem key_mem_project_pts
    {a : AbsObjSensHeap} {v : Var} {key : ObjSensKey}
    (h : key ∈ a.pts v) :
    key.site ∈ (projectObjSensHeap a).pts v := by
  simp [projectObjSensHeap]
  exact ⟨key, h, rfl⟩

theorem key_heap_le_project
    {a : AbsObjSensHeap} {key : ObjSensKey} {f : Field}
    (hkey : key ∈ keysForSite (a.pts 0) key.site) :
    Label.le (a.heap key f) ((projectObjSensHeap a).heap key.site f) := by
  unfold projectObjSensHeap
  simp [joinKeyHeap]
  have hmem : a.heap key f ∈ (keysForSite (a.pts 0) key.site).map (fun k => a.heap k f) :=
    List.mem_map.mpr ⟨key, hkey, rfl⟩
  exact mem_le_joinLabels hmem

/-!
The following projection theorem is intentionally stated with a coverage
condition for heap keys.  In a real object-sensitive analysis this coverage comes
from allocation/call-graph construction.
-/
def ObjSensHeapCoverage (c : ConcreteAllocHeap) (a : AbsObjSensHeap) : Prop :=
  forall o,
    exists key,
      key ∈ keysForSite (a.pts 0) (c.siteOf o) /\
      key.site = c.siteOf o

theorem object_sensitive_projects_to_alloc_sound
    {c : ConcreteAllocHeap} {a : AbsObjSensHeap}
    (hs : ObjSensHeapSound c a)
    (hcov : ObjSensHeapCoverage c a) :
    AllocHeapSound c (projectObjSensHeap a) := by
  constructor
  · intro v
    exact hs.varSound v
  · intro v
    rcases hs.ptsSound v with ⟨key, hmem, hsite⟩
    rw [← hsite]
    exact key_mem_project_pts hmem
  · intro o f
    rcases hcov o with ⟨key, hkey, hsite⟩
    have hheap := hs.heapSound o f key hsite (Or.inr trivial)
    have hkey' : key ∈ keysForSite (a.pts 0) key.site := by
      rwa [hsite]
    have hproj := key_heap_le_project (a := a) (key := key) (f := f) hkey'
    rw [hsite] at hproj
    exact Label.le_trans hheap hproj

/-! ## Demo -/

def objKey : ObjSensKey := { site := 7, ctx := 100 }

def objSensAbstract : AbsObjSensHeap :=
  { vars := allocAbstract.vars
  , pts := fun _ => [objKey]
  , heap := fun _ _ => Label.clean
  }

theorem objSensDemoSound : ObjSensHeapSound allocConcrete objSensAbstract := by
  constructor
  · intro v
    exact allocDemoSound.varSound v
  · intro v
    refine ⟨objKey, ?_, ?_⟩
    · simp [objSensAbstract]
    · simp [objKey, allocConcrete]
  · intro o f key _ _
    simp [objSensAbstract]
    exact allocDemoSound.heapSound o f

theorem objSensDemoCoverage : ObjSensHeapCoverage allocConcrete objSensAbstract := by
  intro o
  refine ⟨objKey, ?_, ?_⟩
  · simp [keysForSite, objSensAbstract, objKey, allocConcrete]
  · simp [objKey, allocConcrete]

example :
    AllocHeapSound allocConcrete (projectObjSensHeap objSensAbstract) :=
  object_sensitive_projects_to_alloc_sound objSensDemoSound objSensDemoCoverage

end PcSastLean
