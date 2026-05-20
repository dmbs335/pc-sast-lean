import PcSastLean.RichSourceProvenance

/-!
Mini source-language branch extraction.

`MiniSourceExtraction` proves exact extraction for straight-line mini source
programs.  This module adds a structured source-level branch slice: concrete
execution chooses one branch, while the abstract checker executes both branches
and joins their stores/results.  This brings branch/join reasoning closer to the
source-extraction layer instead of leaving it only in the low-level IR modules.

Claim boundary:

* Verified here: for the mini source language, concrete branch execution is
  covered by abstract branch/join execution, and source-level branch safety
  follows from abstract branch safety.
* External obligations: production extractors must model real conditions,
  dominance/control dependence, exception edges, callbacks, and async scheduling.
* Not modeled here: path-sensitive branch feasibility or real language
  control-flow graph construction.
-/

namespace PcSastLean

namespace Protection

theorem meet_le_left (l r : Protection) : le (meet l r) l := by
  intro k h
  cases k <;> simp [has, meet] at h ⊢
  · exact h.left
  · exact h.left
  · exact h.left
  · exact h.left

theorem meet_le_right (l r : Protection) : le (meet l r) r := by
  intro k h
  cases k <;> simp [has, meet] at h ⊢
  · exact h.right
  · exact h.right
  · exact h.right
  · exact h.right

theorem le_trans {a b c : Protection}
    (hab : le a b) (hbc : le b c) :
    le a c := by
  intro k h
  exact hbc k (hab k h)

end Protection

namespace SecLabel

theorem sound_trans {a b c : SecLabel}
    (hab : Sound a b) (hbc : Sound b c) :
    Sound a c := by
  cases a with
  | untrusted ap =>
      cases b with
      | untrusted bp =>
          cases c with
          | untrusted cp =>
              exact Protection.le_trans hbc hab

theorem sound_combine_left (l r : SecLabel) :
    Sound l (combine l r) := by
  cases l with
  | untrusted lp =>
      cases r with
      | untrusted rp =>
          exact Protection.meet_le_left lp rp

theorem sound_combine_right (l r : SecLabel) :
    Sound r (combine l r) := by
  cases l with
  | untrusted lp =>
      cases r with
      | untrusted rp =>
          exact Protection.meet_le_right lp rp

end SecLabel

namespace SecStore

def join (l r : SecStore) : SecStore :=
  fun v => SecLabel.combine (l v) (r v)

theorem sound_trans {a b c : SecStore}
    (hab : SecStore.Sound a b) (hbc : SecStore.Sound b c) :
    SecStore.Sound a c := by
  intro v
  exact SecLabel.sound_trans (hab v) (hbc v)

theorem sound_join_left (l r : SecStore) :
    SecStore.Sound l (join l r) := by
  intro v
  exact SecLabel.sound_combine_left (l v) (r v)

theorem sound_join_right (l r : SecStore) :
    SecStore.Sound r (join l r) := by
  intro v
  exact SecLabel.sound_combine_right (l v) (r v)

end SecStore

theorem miniExec_sound
    {concrete abstract : SecStore}
    (hs : SecStore.Sound concrete abstract)
    (prog : List MiniStmt) :
    SecStore.Sound (miniExec concrete prog).1 (miniExec abstract prog).1 /\
    ListSubset (miniExec concrete prog).2 (miniExec abstract prog).2 := by
  rw [miniExec_compile_exact concrete prog, miniExec_compile_exact abstract prog]
  exact sexec_sound (compileMini prog) hs

def miniExecConcreteBranch
    (chooseThen : Bool) (s : SecStore)
    (thenProg elseProg : List MiniStmt) : SecStore × List Node :=
  if chooseThen then miniExec s thenProg else miniExec s elseProg

def miniExecAbstractBranch
    (s : SecStore)
    (thenProg elseProg : List MiniStmt) : SecStore × List Node :=
  let thenResult := miniExec s thenProg
  let elseResult := miniExec s elseProg
  (SecStore.join thenResult.1 elseResult.1, thenResult.2 ++ elseResult.2)

theorem mini_branch_sound
    {concrete abstract : SecStore}
    {thenProg elseProg : List MiniStmt}
    (chooseThen : Bool)
    (hs : SecStore.Sound concrete abstract) :
    SecStore.Sound
      (miniExecConcreteBranch chooseThen concrete thenProg elseProg).1
      (miniExecAbstractBranch abstract thenProg elseProg).1 /\
    ListSubset
      (miniExecConcreteBranch chooseThen concrete thenProg elseProg).2
      (miniExecAbstractBranch abstract thenProg elseProg).2 := by
  cases chooseThen
  · have helse := miniExec_sound hs elseProg
    constructor
    · unfold miniExecConcreteBranch miniExecAbstractBranch
      simp
      exact SecStore.sound_trans helse.left
        (SecStore.sound_join_right
          (miniExec abstract thenProg).1
          (miniExec abstract elseProg).1)
    · unfold miniExecConcreteBranch miniExecAbstractBranch
      simp
      exact ListSubset.trans helse.right ListSubset.append_right
  · have hthen := miniExec_sound hs thenProg
    constructor
    · unfold miniExecConcreteBranch miniExecAbstractBranch
      simp
      exact SecStore.sound_trans hthen.left
        (SecStore.sound_join_left
          (miniExec abstract thenProg).1
          (miniExec abstract elseProg).1)
    · unfold miniExecConcreteBranch miniExecAbstractBranch
      simp
      exact ListSubset.trans hthen.right ListSubset.append_left

theorem mini_branch_abstract_safety_implies_concrete_safety
    {concrete abstract : SecStore}
    {thenProg elseProg : List MiniStmt}
    (chooseThen : Bool)
    (hs : SecStore.Sound concrete abstract)
    (habs : forall id : Node,
      id ∉ (miniExecAbstractBranch abstract thenProg elseProg).2) :
    forall id : Node,
      id ∉ (miniExecConcreteBranch chooseThen concrete thenProg elseProg).2 := by
  intro id hbad
  exact habs id ((mini_branch_sound chooseThen hs).right id hbad)

/-! ## Demo -/

def miniBranchThenBug : List MiniStmt :=
  [ miniInput 0
  , miniSink 0 SinkKind.html 801
  ]

def miniBranchElsePatched : List MiniStmt :=
  [ miniInput 0
  , miniSanitize 1 0 SinkKind.html
  , miniSink 1 SinkKind.html 801
  ]

example :
    (miniExecConcreteBranch true emptySecStore
      miniBranchThenBug miniBranchElsePatched).2 = [801] := by
  native_decide

example :
    (miniExecConcreteBranch false emptySecStore
      miniBranchThenBug miniBranchElsePatched).2 = [] := by
  native_decide

example :
    (miniExecAbstractBranch emptySecStore
      miniBranchThenBug miniBranchElsePatched).2 = [801] := by
  native_decide

example :
    forall id : Node,
      id ∉ (miniExecConcreteBranch false emptySecStore
        miniBranchElsePatched miniBranchElsePatched).2 :=
  mini_branch_abstract_safety_implies_concrete_safety
    (chooseThen := false)
    (concrete := emptySecStore)
    (abstract := emptySecStore)
    (thenProg := miniBranchElsePatched)
    (elseProg := miniBranchElsePatched)
    (SecStore.sound_refl emptySecStore)
    (by native_decide)

end PcSastLean
