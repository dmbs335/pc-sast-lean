import PcSastLean.MiniSourceBranch

/-!
Mini source-language exception flow.

This module adds a small source-level try/catch/finally slice.  Concrete
execution follows either the protected path or the handler path.  Abstract
execution analyzes both paths, joins their stores/findings, then executes the
finally block.  This is still a toy exception model, but it moves exception-flow
reasoning out of an opaque summary assumption for the mini source language.

Claim boundary:

* Verified here: concrete mini try/catch/finally execution is covered by
  abstract execution that analyzes both protected and handler paths.
* External obligations: production extractors must recover real exception edges,
  implicit throws, async rejection paths, and framework error handlers.
* Not modeled here: stack unwinding, typed exceptions, resource cleanup
  semantics, promises, async/await, or language-specific exception rules.
-/

namespace PcSastLean

def miniExecConcreteTryCatch
    (throws : Bool) (s : SecStore)
    (tryProg catchProg : List MiniStmt) : SecStore × List Node :=
  if throws then miniExec s catchProg else miniExec s tryProg

def miniExecAbstractTryCatch
    (s : SecStore)
    (tryProg catchProg : List MiniStmt) : SecStore × List Node :=
  miniExecAbstractBranch s tryProg catchProg

theorem mini_try_catch_sound
    {concrete abstract : SecStore}
    {tryProg catchProg : List MiniStmt}
    (throws : Bool)
    (hs : SecStore.Sound concrete abstract) :
    SecStore.Sound
      (miniExecConcreteTryCatch throws concrete tryProg catchProg).1
      (miniExecAbstractTryCatch abstract tryProg catchProg).1 /\
    ListSubset
      (miniExecConcreteTryCatch throws concrete tryProg catchProg).2
      (miniExecAbstractTryCatch abstract tryProg catchProg).2 := by
  cases throws
  · exact mini_branch_sound true hs
  · exact mini_branch_sound false hs

def miniExecConcreteTryCatchFinally
    (throws : Bool) (s : SecStore)
    (tryProg catchProg finallyProg : List MiniStmt) : SecStore × List Node :=
  let chosen := miniExecConcreteTryCatch throws s tryProg catchProg
  let fin := miniExec chosen.1 finallyProg
  (fin.1, chosen.2 ++ fin.2)

def miniExecAbstractTryCatchFinally
    (s : SecStore)
    (tryProg catchProg finallyProg : List MiniStmt) : SecStore × List Node :=
  let joined := miniExecAbstractTryCatch s tryProg catchProg
  let fin := miniExec joined.1 finallyProg
  (fin.1, joined.2 ++ fin.2)

theorem mini_try_catch_finally_sound
    {concrete abstract : SecStore}
    {tryProg catchProg finallyProg : List MiniStmt}
    (throws : Bool)
    (hs : SecStore.Sound concrete abstract) :
    SecStore.Sound
      (miniExecConcreteTryCatchFinally throws concrete tryProg catchProg finallyProg).1
      (miniExecAbstractTryCatchFinally abstract tryProg catchProg finallyProg).1 /\
    ListSubset
      (miniExecConcreteTryCatchFinally throws concrete tryProg catchProg finallyProg).2
      (miniExecAbstractTryCatchFinally abstract tryProg catchProg finallyProg).2 := by
  have hprotected := mini_try_catch_sound
    (throws := throws)
    (tryProg := tryProg)
    (catchProg := catchProg)
    hs
  have hfinally := miniExec_sound hprotected.left finallyProg
  constructor
  · unfold miniExecConcreteTryCatchFinally miniExecAbstractTryCatchFinally
    exact hfinally.left
  · unfold miniExecConcreteTryCatchFinally miniExecAbstractTryCatchFinally
    exact append_subset_append hprotected.right hfinally.right

theorem mini_try_catch_finally_abstract_safety_implies_concrete_safety
    {concrete abstract : SecStore}
    {tryProg catchProg finallyProg : List MiniStmt}
    (throws : Bool)
    (hs : SecStore.Sound concrete abstract)
    (habs : forall id : Node,
      id ∉ (miniExecAbstractTryCatchFinally abstract tryProg catchProg finallyProg).2) :
    forall id : Node,
      id ∉ (miniExecConcreteTryCatchFinally throws concrete tryProg catchProg finallyProg).2 := by
  intro id hbad
  exact habs id ((mini_try_catch_finally_sound throws hs).right id hbad)

/-! ## Demo -/

def miniTryBug : List MiniStmt :=
  [ miniInput 0
  , miniSink 0 SinkKind.html 901
  ]

def miniCatchPatch : List MiniStmt :=
  [ miniInput 0
  , miniSanitize 1 0 SinkKind.html
  , miniSink 1 SinkKind.html 901
  ]

def miniFinallySafe : List MiniStmt :=
  [ miniSanitize 2 0 SinkKind.html
  , miniSink 2 SinkKind.html 902
  ]

example :
    (miniExecConcreteTryCatchFinally false emptySecStore
      miniTryBug miniCatchPatch miniFinallySafe).2 = [901] := by
  native_decide

example :
    (miniExecConcreteTryCatchFinally true emptySecStore
      miniTryBug miniCatchPatch miniFinallySafe).2 = [] := by
  native_decide

example :
    (miniExecAbstractTryCatchFinally emptySecStore
      miniTryBug miniCatchPatch miniFinallySafe).2 = [901] := by
  native_decide

example :
    forall id : Node,
      id ∉ (miniExecConcreteTryCatchFinally true emptySecStore
        miniCatchPatch miniCatchPatch miniFinallySafe).2 :=
  mini_try_catch_finally_abstract_safety_implies_concrete_safety
    (throws := true)
    (concrete := emptySecStore)
    (abstract := emptySecStore)
    (tryProg := miniCatchPatch)
    (catchProg := miniCatchPatch)
    (finallyProg := miniFinallySafe)
    (SecStore.sound_refl emptySecStore)
    (by native_decide)

end PcSastLean
