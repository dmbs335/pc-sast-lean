import PcSastLean.MiniSourceException

/-!
Mini source-language callback flow.

This module adds a small callback/event slice.  Concrete execution runs the main
program and may or may not later invoke a registered callback.  Abstract
execution analyzes the main program and the possible callback invocation, then
joins the resulting stores and findings.  This is not a full event-loop
semantics, but it makes one callback-flow obligation explicit for the mini source
language.

Claim boundary:

* Verified here: concrete optional callback execution is covered by abstract
  execution that includes the possible callback path.
* External obligations: production extractors must recover callback
  registrations, event ordering, async scheduling, promise chains, and framework
  lifecycle hooks.
* Not modeled here: event-loop fairness, concurrency, cancellation, reentrancy,
  shared mutable scheduling state, or async/await semantics.
-/

namespace PcSastLean

structure MiniCallback where
  registeredAt : AstNodeId
  body : List MiniStmt
deriving Repr

def miniExecConcreteCallback
    (fires : Bool) (s : SecStore)
    (mainProg : List MiniStmt) (callback : MiniCallback) : SecStore × List Node :=
  let main := miniExec s mainProg
  if fires then
    let cb := miniExec main.1 callback.body
    (cb.1, main.2 ++ cb.2)
  else
    main

def miniExecAbstractCallback
    (s : SecStore)
    (mainProg : List MiniStmt) (callback : MiniCallback) : SecStore × List Node :=
  let main := miniExec s mainProg
  let cb := miniExec main.1 callback.body
  (SecStore.join main.1 cb.1, main.2 ++ cb.2)

theorem mini_callback_sound
    {concrete abstract : SecStore}
    {mainProg : List MiniStmt} {callback : MiniCallback}
    (fires : Bool)
    (hs : SecStore.Sound concrete abstract) :
    SecStore.Sound
      (miniExecConcreteCallback fires concrete mainProg callback).1
      (miniExecAbstractCallback abstract mainProg callback).1 /\
    ListSubset
      (miniExecConcreteCallback fires concrete mainProg callback).2
      (miniExecAbstractCallback abstract mainProg callback).2 := by
  have hmain := miniExec_sound hs mainProg
  cases fires
  · constructor
    · unfold miniExecConcreteCallback miniExecAbstractCallback
      simp
      exact SecStore.sound_trans hmain.left
        (SecStore.sound_join_left
          (miniExec abstract mainProg).1
          (miniExec (miniExec abstract mainProg).1 callback.body).1)
    · unfold miniExecConcreteCallback miniExecAbstractCallback
      simp
      exact ListSubset.trans hmain.right ListSubset.append_left
  · have hcb := miniExec_sound hmain.left callback.body
    constructor
    · unfold miniExecConcreteCallback miniExecAbstractCallback
      simp
      exact SecStore.sound_trans hcb.left
        (SecStore.sound_join_right
          (miniExec abstract mainProg).1
          (miniExec (miniExec abstract mainProg).1 callback.body).1)
    · unfold miniExecConcreteCallback miniExecAbstractCallback
      simp
      exact append_subset_append hmain.right hcb.right

theorem mini_callback_abstract_safety_implies_concrete_safety
    {concrete abstract : SecStore}
    {mainProg : List MiniStmt} {callback : MiniCallback}
    (fires : Bool)
    (hs : SecStore.Sound concrete abstract)
    (habs : forall id : Node,
      id ∉ (miniExecAbstractCallback abstract mainProg callback).2) :
    forall id : Node,
      id ∉ (miniExecConcreteCallback fires concrete mainProg callback).2 := by
  intro id hbad
  exact habs id ((mini_callback_sound fires hs).right id hbad)

/-! ## Demo -/

def miniCallbackMain : List MiniStmt :=
  [ miniInput 0 ]

def miniUnsafeCallback : MiniCallback :=
  { registeredAt := 100
  , body := [miniSink 0 SinkKind.html 1001]
  }

def miniSafeCallback : MiniCallback :=
  { registeredAt := 101
  , body :=
      [ miniSanitize 1 0 SinkKind.html
      , miniSink 1 SinkKind.html 1001
      ]
  }

example :
    (miniExecConcreteCallback true emptySecStore
      miniCallbackMain miniUnsafeCallback).2 = [1001] := by
  native_decide

example :
    (miniExecConcreteCallback false emptySecStore
      miniCallbackMain miniUnsafeCallback).2 = [] := by
  native_decide

example :
    (miniExecAbstractCallback emptySecStore
      miniCallbackMain miniUnsafeCallback).2 = [1001] := by
  native_decide

example :
    forall id : Node,
      id ∉ (miniExecConcreteCallback true emptySecStore
        miniCallbackMain miniSafeCallback).2 :=
  mini_callback_abstract_safety_implies_concrete_safety
    (fires := true)
    (concrete := emptySecStore)
    (abstract := emptySecStore)
    (mainProg := miniCallbackMain)
    (callback := miniSafeCallback)
    (SecStore.sound_refl emptySecStore)
    (by native_decide)

end PcSastLean
