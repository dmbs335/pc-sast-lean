import PcSastLean.PointerArithmetic
import PcSastLean.CIGate

/-!
Pointer-disjoint false-positive suppression.

May-alias abstraction is sound because it writes through every possible pointer.
That same over-approximation can create a false positive: an abstract write may
taint the location later read by a sink even when the concrete write pointer and
read pointer are different.

This module proves a small but engineering-shaped precision theorem for that
case.  A checked certificate based on concrete offset-pointer disjointness and a
clean concrete read target is enough to suppress the abstract alias finding
without hiding a concrete bug.

Claim boundary:

* Verified here: in the base+offset model, pointer-disjoint write/read evidence
  proves a may-alias finding is absent from concrete execution.
* External obligations: production C/C++/unsafe-language extractors must justify
  pointer provenance, object layout, bounds, casts, and memory model assumptions.
* Not modeled here: negative offsets, byte-level overlap, type punning,
  concurrency, UB, realloc/free, or partial-field overlap.
-/

namespace PcSastLean

def concreteWriteLoadSink
    (s : ConcreteOffsetHeap)
    (writeBase src readBase dst sink : Var) : List Node :=
  let afterWrite := s.setMem (s.pointsTo writeBase) (s.vars src)
  let afterLoad := afterWrite.setVar dst (afterWrite.mem (afterWrite.pointsTo readBase))
  if afterLoad.vars dst = Label.tainted then [sink] else []

def abstractWriteLoadSink
    (s : AbsOffsetHeap)
    (writeBase src readBase dst sink : Var) : List Node :=
  let afterWrite := s.writeMayPtr writeBase (s.vars src)
  let afterLoad := afterWrite.setVar dst (readAbsPtr afterWrite readBase)
  if afterLoad.vars dst = Label.tainted then [sink] else []

theorem pointer_disjoint_write_load_not_concrete
    {s : ConcreteOffsetHeap}
    {writeBase src readBase dst sink : Var}
    (hdisjoint : s.pointsTo writeBase ≠ s.pointsTo readBase)
    (hclean : s.mem (s.pointsTo readBase) = Label.clean) :
    sink ∉ concreteWriteLoadSink s writeBase src readBase dst sink := by
  unfold concreteWriteLoadSink
  have hneq : s.pointsTo readBase ≠ s.pointsTo writeBase := by
    intro h
    exact hdisjoint h.symm
  simp [ConcreteOffsetHeap.setMem, ConcreteOffsetHeap.setVar, hneq, hclean]

structure PointerDisjointEvidence where
  writeBase : Var
  src : Var
  readBase : Var
  dst : Var
  sink : Node
deriving DecidableEq, Repr

def PointerDisjointEvidence.Valid
    (s : ConcreteOffsetHeap) (e : PointerDisjointEvidence) : Prop :=
  s.pointsTo e.writeBase ≠ s.pointsTo e.readBase /\
  s.mem (s.pointsTo e.readBase) = Label.clean

def checkPointerDisjointEvidence
    (s : ConcreteOffsetHeap) (e : PointerDisjointEvidence) : Bool :=
  decide (s.pointsTo e.writeBase ≠ s.pointsTo e.readBase) &&
  decide (s.mem (s.pointsTo e.readBase) = Label.clean)

theorem checkPointerDisjointEvidence_sound
    {s : ConcreteOffsetHeap} {e : PointerDisjointEvidence}
    (h : checkPointerDisjointEvidence s e = true) :
    e.Valid s := by
  simp [checkPointerDisjointEvidence, PointerDisjointEvidence.Valid] at h
  exact h

theorem checked_pointer_disjoint_not_concrete
    {s : ConcreteOffsetHeap} {e : PointerDisjointEvidence}
    (h : checkPointerDisjointEvidence s e = true) :
    e.sink ∉
      concreteWriteLoadSink s e.writeBase e.src e.readBase e.dst e.sink := by
  exact pointer_disjoint_write_load_not_concrete
    (s := s)
    (writeBase := e.writeBase)
    (src := e.src)
    (readBase := e.readBase)
    (dst := e.dst)
    (sink := e.sink)
    (checkPointerDisjointEvidence_sound h).left
    (checkPointerDisjointEvidence_sound h).right

def pointerDisjointTriageEvidence
    (s : ConcreteOffsetHeap) (e : PointerDisjointEvidence)
    (_h : checkPointerDisjointEvidence s e = true) : TriageEvidence :=
  { sink := e.sink
  , impossible := e.Valid s
  }

theorem pointerDisjointTriageEvidence_sound
    (s : ConcreteOffsetHeap) (e : PointerDisjointEvidence)
    (h : checkPointerDisjointEvidence s e = true) :
    EvidenceSound
      (concreteWriteLoadSink s e.writeBase e.src e.readBase e.dst e.sink)
      (pointerDisjointTriageEvidence s e h) := by
  intro hvalid
  exact pointer_disjoint_write_load_not_concrete hvalid.left hvalid.right

/-! ## Demo: abstract may-alias false positive, concrete disjointness -/

def pointerDisjointConcrete : ConcreteOffsetHeap :=
  { vars := fun v => if v = 1 then Label.tainted else Label.clean
  , pointsTo := fun v => if v = 10 then offsetPtr0 else offsetPtr4
  , mem := fun _ => Label.clean
  }

def pointerDisjointAbstract : AbsOffsetHeap :=
  { vars := fun v => if v = 1 then Label.tainted else Label.clean
  , ptrs := fun v =>
      if v = 10 then [offsetPtr0, offsetPtr4]
      else if v = 20 then [offsetPtr4]
      else [offsetPtr4]
  , mem := fun _ => Label.clean
  }

def pointerDisjointFinding : Node := 1301

def pointerDisjointEvidence : PointerDisjointEvidence :=
  { writeBase := 10
  , src := 1
  , readBase := 20
  , dst := 30
  , sink := pointerDisjointFinding
  }

example :
    checkPointerDisjointEvidence
      pointerDisjointConcrete pointerDisjointEvidence = true := by
  native_decide

example :
    concreteWriteLoadSink
      pointerDisjointConcrete 10 1 20 30 pointerDisjointFinding = [] := by
  native_decide

example :
    abstractWriteLoadSink
      pointerDisjointAbstract 10 1 20 30 pointerDisjointFinding =
        [pointerDisjointFinding] := by
  native_decide

def pointerDisjointRun : AnalyzerRun :=
  { concrete :=
      concreteWriteLoadSink
        pointerDisjointConcrete 10 1 20 30 pointerDisjointFinding
  , abstract :=
      abstractWriteLoadSink
        pointerDisjointAbstract 10 1 20 30 pointerDisjointFinding
  }

theorem pointerDisjointRunSound : pointerDisjointRun.Sound := by
  intro sink hconcrete
  have hnone : pointerDisjointRun.concrete = [] := by
    native_decide
  rw [hnone] at hconcrete
  cases hconcrete

def pointerDisjointTriageEvidenceDemo : TriageEvidence :=
  pointerDisjointTriageEvidence
    pointerDisjointConcrete
    pointerDisjointEvidence
    (by native_decide)

theorem pointerDisjointTriageEvidenceDemoSound :
    EvidenceSound pointerDisjointRun.concrete pointerDisjointTriageEvidenceDemo := by
  unfold pointerDisjointRun pointerDisjointTriageEvidenceDemo
  exact pointerDisjointTriageEvidence_sound
    pointerDisjointConcrete
    pointerDisjointEvidence
    (by native_decide)

def pointerDisjointTriage : TriageRun :=
  { report := []
  , suppressed := [pointerDisjointFinding]
  , evidence := [pointerDisjointTriageEvidenceDemo]
  }

theorem pointerDisjointTriageComplete :
    pointerDisjointTriage.Complete pointerDisjointRun := by
  intro sink habs
  right
  have habsList : pointerDisjointRun.abstract = [pointerDisjointFinding] := by
    native_decide
  rw [habsList] at habs
  have hsink : sink = pointerDisjointFinding := by
    simpa [pointerDisjointFinding] using habs
  subst hsink
  constructor
  · simp [pointerDisjointTriage, pointerDisjointFinding]
  · refine ⟨pointerDisjointTriageEvidenceDemo, ?_, ?_, ?_, ?_⟩
    · simp [pointerDisjointTriage]
    · simp [pointerDisjointTriageEvidenceDemo, pointerDisjointTriageEvidence,
        pointerDisjointEvidence, pointerDisjointFinding]
    · exact checkPointerDisjointEvidence_sound
        (s := pointerDisjointConcrete)
        (e := pointerDisjointEvidence)
        (by native_decide)
    · exact pointerDisjointTriageEvidenceDemoSound

example : ListSubset pointerDisjointRun.concrete pointerDisjointTriage.report :=
  ci_gate_no_bug_hiding pointerDisjointRunSound pointerDisjointTriageComplete

end PcSastLean
