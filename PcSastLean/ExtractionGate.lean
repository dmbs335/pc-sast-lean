import PcSastLean.SuppressionGate

/-!
Extraction gates.

All previous gates are strong only after code has been extracted into a trusted
IR.  Real SAST lives or dies at this boundary: framework routes, generated code,
templates, language ASTs, source maps, and build configuration must all be
represented soundly.

This module states the bridge explicitly.  An extractor certificate must prove
that every source-level vulnerability is represented by the IR-level concrete
violations.  Once that is true, fix, baseline, and suppression gates transfer
from IR results back to source code.

Claim boundary:

* Verified here: if `SourceToIRSound` is supplied, IR-level fix, baseline, and
  suppression gates transfer to source-level violation lists.
* External obligations: real extractors must prove `SourceToIRSound` for their
  source language, framework, generated code, source maps, and build settings.
* Not modeled here: a production JavaScript, TypeScript, Python, Java, or C/C++
  source semantics.
-/

namespace PcSastLean

def SourceToIRSound (sourceViolations irViolations : List Node) : Prop :=
  ListSubset sourceViolations irViolations

theorem extraction_fix_gate
    {sourceViolations irViolations : List Node} {sink : Node}
    (hextract : SourceToIRSound sourceViolations irViolations)
    (hir : sink ∉ irViolations) :
    sink ∉ sourceViolations := by
  intro hsource
  exact hir (hextract sink hsource)

theorem extraction_baseline_gate
    {sourceViolations irViolations baseline : List Node}
    (hextract : SourceToIRSound sourceViolations irViolations)
    (hir : NoNewConcreteViolations irViolations baseline) :
    NoNewConcreteViolations sourceViolations baseline := by
  exact ListSubset.trans hextract hir

theorem extraction_suppression_gate
    {sourceViolations irConcrete irAbstract report suppressed : List Node}
    (hextract : SourceToIRSound sourceViolations irConcrete)
    (hsound : ListSubset irConcrete irAbstract)
    (hcover : ReportCoversUnsuppressed irAbstract report suppressed)
    (hsupp : SoundSuppression irConcrete suppressed) :
    ListSubset sourceViolations report := by
  exact ListSubset.trans hextract (suppression_gate hsound hcover hsupp)

theorem extraction_heap_fix_gate
    {sourceViolations : List Node}
    {concrete : ConcreteHeapState} {abstract : AbsHeapState}
    {prog : List HInstr} {sink : Node}
    (hextract : SourceToIRSound sourceViolations (execConcreteHeap concrete prog).2)
    (hs : HeapSound concrete abstract)
    (habs : SinkRemoved sink (execAbsHeap abstract prog).2) :
    sink ∉ sourceViolations := by
  exact extraction_fix_gate hextract (fix_gate_heap hs habs)

theorem extraction_sanitizer_fix_gate
    {sourceViolations : List Node}
    {concrete abstract : SecStore}
    {prog : List SInstr} {sink : Node}
    (hextract : SourceToIRSound sourceViolations (sexec concrete prog).2)
    (hs : SecStore.Sound concrete abstract)
    (habs : sink ∉ (sexec abstract prog).2) :
    sink ∉ sourceViolations := by
  exact extraction_fix_gate hextract (sanitizer_fix_gate hs habs)

/-! ## A tiny source language demo -/

inductive SourceStmt where
  | input (dst : Var)
  | escape (dst src : Var) (kind : SinkKind)
  | output (src : Var) (kind : SinkKind) (id : Node)
deriving DecidableEq, Repr

def compileSourceStmt : SourceStmt -> SInstr
  | SourceStmt.input dst => SInstr.source dst
  | SourceStmt.escape dst src kind => SInstr.sanitize dst src kind
  | SourceStmt.output src kind id => SInstr.sink src kind id

def compileSource (p : List SourceStmt) : List SInstr :=
  p.map compileSourceStmt

def sourceExec (s : SecStore) (p : List SourceStmt) : SecStore × List Node :=
  sexec s (compileSource p)

theorem compileSource_exact
    (s : SecStore) (p : List SourceStmt) :
    SourceToIRSound (sourceExec s p).2 (sexec s (compileSource p)).2 := by
  intro id h
  exact h

def sourceHtmlBug : List SourceStmt :=
  [ SourceStmt.input 0
  , SourceStmt.escape 1 0 SinkKind.sql
  , SourceStmt.output 1 SinkKind.html 51
  ]

def sourceHtmlPatch : List SourceStmt :=
  [ SourceStmt.input 0
  , SourceStmt.escape 1 0 SinkKind.html
  , SourceStmt.output 1 SinkKind.html 51
  ]

example : (sourceExec emptySecStore sourceHtmlBug).2 = [51] := by
  native_decide

example : (sourceExec emptySecStore sourceHtmlPatch).2 = [] := by
  native_decide

example :
    51 ∉ (sourceExec emptySecStore sourceHtmlPatch).2 :=
  extraction_sanitizer_fix_gate
    (compileSource_exact emptySecStore sourceHtmlPatch)
    (SecStore.sound_refl emptySecStore)
    (by native_decide)

end PcSastLean
