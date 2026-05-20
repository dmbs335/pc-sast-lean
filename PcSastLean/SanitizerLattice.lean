import PcSastLean.DynamicObligations

/-!
Context-sensitive sanitizer lattice.

The earlier IR had a single `sanitize` instruction that turned tainted data into
clean data.  Real SAST cannot do that: SQL escaping does not make a value safe
for HTML, and HTML escaping does not make it safe for a shell command.

This module models taint as a set of missing protections.  A sink is safe only
when its required protection is present.  The key engineering theorem is that
sanitizers are context-specific by construction.
-/

namespace PcSastLean

inductive SinkKind where
  | sql
  | html
  | shell
  | path
deriving DecidableEq, Repr

structure Protection where
  sqlSafe : Bool
  htmlSafe : Bool
  shellSafe : Bool
  pathSafe : Bool
deriving DecidableEq, Repr

namespace Protection

def bottom : Protection :=
  { sqlSafe := false, htmlSafe := false, shellSafe := false, pathSafe := false }

def top : Protection :=
  { sqlSafe := true, htmlSafe := true, shellSafe := true, pathSafe := true }

def has (p : Protection) : SinkKind -> Bool
  | SinkKind.sql => p.sqlSafe
  | SinkKind.html => p.htmlSafe
  | SinkKind.shell => p.shellSafe
  | SinkKind.path => p.pathSafe

def add (p : Protection) : SinkKind -> Protection
  | SinkKind.sql => { p with sqlSafe := true }
  | SinkKind.html => { p with htmlSafe := true }
  | SinkKind.shell => { p with shellSafe := true }
  | SinkKind.path => { p with pathSafe := true }

def meet (l r : Protection) : Protection :=
  { sqlSafe := l.sqlSafe && r.sqlSafe
  , htmlSafe := l.htmlSafe && r.htmlSafe
  , shellSafe := l.shellSafe && r.shellSafe
  , pathSafe := l.pathSafe && r.pathSafe
  }

def le (l r : Protection) : Prop :=
  forall k, l.has k = true -> r.has k = true

theorem le_refl (p : Protection) : le p p := by
  intro _ h
  exact h

theorem add_le {l r : Protection} (h : le l r) (k : SinkKind) :
    le (l.add k) (r.add k) := by
  cases k <;>
    intro need hneed <;>
    cases need <;>
    simp [has, add] at hneed ⊢
  all_goals first
    | exact h SinkKind.sql hneed
    | exact h SinkKind.html hneed
    | exact h SinkKind.shell hneed
    | exact h SinkKind.path hneed

theorem meet_le {l₁ l₂ r₁ r₂ : Protection}
    (h₁ : le l₁ r₁) (h₂ : le l₂ r₂) :
    le (meet l₁ l₂) (meet r₁ r₂) := by
  intro need hneed
  cases need <;> simp [has, meet] at hneed ⊢
  · exact And.intro (h₁ SinkKind.sql hneed.left) (h₂ SinkKind.sql hneed.right)
  · exact And.intro (h₁ SinkKind.html hneed.left) (h₂ SinkKind.html hneed.right)
  · exact And.intro (h₁ SinkKind.shell hneed.left) (h₂ SinkKind.shell hneed.right)
  · exact And.intro (h₁ SinkKind.path hneed.left) (h₂ SinkKind.path hneed.right)

theorem add_has (p : Protection) (k : SinkKind) :
    (add p k).has k = true := by
  cases k <;> simp [add, has]

theorem add_preserves {p : Protection} {need got : SinkKind}
    (h : p.has need = true) :
    (p.add got).has need = true := by
  cases need <;> cases got <;> simp [has, add] at h ⊢ <;> exact h

theorem meet_has {l r : Protection} {k : SinkKind}
    (hl : l.has k = true) (hr : r.has k = true) :
    (meet l r).has k = true := by
  cases k <;> simp [has, meet] at hl hr ⊢ <;> exact And.intro hl hr

end Protection

inductive SecLabel where
  | untrusted : Protection -> SecLabel
deriving DecidableEq, Repr

namespace SecLabel

def input : SecLabel :=
  SecLabel.untrusted Protection.bottom

def trusted : SecLabel :=
  SecLabel.untrusted Protection.top

def sanitize : SecLabel -> SinkKind -> SecLabel
  | SecLabel.untrusted p, k => SecLabel.untrusted (p.add k)

def combine : SecLabel -> SecLabel -> SecLabel
  | SecLabel.untrusted l, SecLabel.untrusted r => SecLabel.untrusted (Protection.meet l r)

def safeFor : SecLabel -> SinkKind -> Prop
  | SecLabel.untrusted p, k => p.has k = true

def safeForBool : SecLabel -> SinkKind -> Bool
  | SecLabel.untrusted p, k => p.has k

def Sound (concrete abstract : SecLabel) : Prop :=
  match concrete, abstract with
  | SecLabel.untrusted cp, SecLabel.untrusted ap => Protection.le ap cp

theorem sanitize_safe_for (l : SecLabel) (k : SinkKind) :
    (sanitize l k).safeFor k := by
  cases l with
  | untrusted p =>
      simp [sanitize, safeFor, Protection.add_has]

theorem sanitize_preserves_existing
    {l : SecLabel} {need got : SinkKind}
    (h : l.safeFor need) :
    (sanitize l got).safeFor need := by
  cases l with
  | untrusted p =>
      exact Protection.add_preserves h

theorem combine_safe_for
    {l r : SecLabel} {k : SinkKind}
    (hl : l.safeFor k) (hr : r.safeFor k) :
    (combine l r).safeFor k := by
  cases l with
  | untrusted lp =>
      cases r with
      | untrusted rp =>
          exact Protection.meet_has hl hr

theorem sound_refl (l : SecLabel) : Sound l l := by
  cases l with
  | untrusted p =>
      exact Protection.le_refl p

theorem sanitize_sound {concrete abstract : SecLabel} {k : SinkKind}
    (hs : Sound concrete abstract) :
    Sound (sanitize concrete k) (sanitize abstract k) := by
  cases concrete with
  | untrusted cp =>
      cases abstract with
      | untrusted ap =>
          exact Protection.add_le hs k

theorem combine_sound
    {c₁ c₂ a₁ a₂ : SecLabel}
    (h₁ : Sound c₁ a₁) (h₂ : Sound c₂ a₂) :
    Sound (combine c₁ c₂) (combine a₁ a₂) := by
  cases c₁ with
  | untrusted cp₁ =>
      cases c₂ with
      | untrusted cp₂ =>
          cases a₁ with
          | untrusted ap₁ =>
              cases a₂ with
              | untrusted ap₂ =>
                  exact Protection.meet_le h₁ h₂

theorem unsafe_sound
    {concrete abstract : SecLabel} {k : SinkKind}
    (hs : Sound concrete abstract)
    (hc : concrete.safeForBool k = false) :
    abstract.safeForBool k = false := by
  cases concrete with
  | untrusted cp =>
      cases abstract with
      | untrusted ap =>
          simp [safeForBool] at hc ⊢
          cases ha : ap.has k
          · rfl
          · have hcTrue := hs k ha
            rw [hc] at hcTrue
            cases hcTrue

end SecLabel

abbrev SecStore := Var -> SecLabel

def SecStore.Sound (concrete abstract : SecStore) : Prop :=
  forall v, SecLabel.Sound (concrete v) (abstract v)

def SecStore.set (s : SecStore) (v : Var) (l : SecLabel) : SecStore :=
  fun v' => if v' = v then l else s v'

theorem SecStore.set_sound
    {concrete abstract : SecStore} {v : Var} {lc la : SecLabel}
    (hs : SecStore.Sound concrete abstract)
    (hl : SecLabel.Sound lc la) :
    SecStore.Sound (SecStore.set concrete v lc) (SecStore.set abstract v la) := by
  intro v'
  unfold SecStore.set
  by_cases h : v' = v
  · simp [h, hl]
  · simp [h, hs v']

theorem SecStore.sound_refl (s : SecStore) : SecStore.Sound s s := by
  intro v
  exact SecLabel.sound_refl (s v)

inductive SInstr where
  | source (dst : Var)
  | assign (dst src : Var)
  | sanitize (dst src : Var) (kind : SinkKind)
  | combine (dst l r : Var)
  | sink (src : Var) (kind : SinkKind) (id : Node)
deriving DecidableEq, Repr

structure SStepResult where
  store : SecStore
  violation : Option Node

def sstep (s : SecStore) : SInstr -> SStepResult
  | SInstr.source dst =>
      { store := s.set dst SecLabel.input, violation := none }
  | SInstr.assign dst src =>
      { store := s.set dst (s src), violation := none }
  | SInstr.sanitize dst src kind =>
      { store := s.set dst (SecLabel.sanitize (s src) kind), violation := none }
  | SInstr.combine dst l r =>
      { store := s.set dst (SecLabel.combine (s l) (s r)), violation := none }
  | SInstr.sink src kind id =>
      { store := s, violation := if (s src).safeForBool kind then none else some id }

def sexec (s : SecStore) : List SInstr -> SecStore × List Node
  | [] => (s, [])
  | i :: rest =>
      let r := sstep s i
      let next := sexec r.store rest
      (next.1, optionViolation r.violation ++ next.2)

theorem sstep_sound
    {concrete abstract : SecStore} {i : SInstr}
    (hs : SecStore.Sound concrete abstract) :
    SecStore.Sound (sstep concrete i).store (sstep abstract i).store /\
    ListSubset (optionViolation (sstep concrete i).violation)
      (optionViolation (sstep abstract i).violation) := by
  cases i with
  | source dst =>
      constructor
      · exact SecStore.set_sound hs (SecLabel.sound_refl SecLabel.input)
      · intro id hmem
        simp [sstep, optionViolation] at hmem
  | assign dst src =>
      constructor
      · exact SecStore.set_sound hs (hs src)
      · intro id hmem
        simp [sstep, optionViolation] at hmem
  | sanitize dst src kind =>
      constructor
      · exact SecStore.set_sound hs (SecLabel.sanitize_sound (hs src))
      · intro id hmem
        simp [sstep, optionViolation] at hmem
  | combine dst l r =>
      constructor
      · exact SecStore.set_sound hs (SecLabel.combine_sound (hs l) (hs r))
      · intro id hmem
        simp [sstep, optionViolation] at hmem
  | sink src kind sinkId =>
      constructor
      · exact hs
      · intro id hmem
        cases hc : (concrete src).safeForBool kind
        · have ha := SecLabel.unsafe_sound (hs src) hc
          simp [sstep, optionViolation, hc, ha] at hmem ⊢
          exact hmem
        · simp [sstep, optionViolation, hc] at hmem

theorem sexec_sound
    {concrete abstract : SecStore} :
    forall prog : List SInstr,
      SecStore.Sound concrete abstract ->
      SecStore.Sound (sexec concrete prog).1 (sexec abstract prog).1 /\
      ListSubset (sexec concrete prog).2 (sexec abstract prog).2 := by
  intro prog
  induction prog generalizing concrete abstract with
  | nil =>
      intro hs
      constructor
      · exact hs
      · intro id hmem
        simp [sexec] at hmem
  | cons i rest ih =>
      intro hs
      have hstep := sstep_sound (i := i) hs
      have htail := ih hstep.left
      constructor
      · simp [sexec]
        exact htail.left
      · intro id hmem
        simp [sexec] at hmem ⊢
        cases hmem with
        | inl hhead =>
            exact Or.inl (hstep.right id hhead)
        | inr hrest =>
            exact Or.inr (htail.right id hrest)

theorem sanitizer_fix_gate
    {concrete abstract : SecStore} {patched : List SInstr} {sink : Node}
    (hs : SecStore.Sound concrete abstract)
    (habs : sink ∉ (sexec abstract patched).2) :
    sink ∉ (sexec concrete patched).2 := by
  intro hbad
  exact habs ((sexec_sound patched hs).right sink hbad)

def emptySecStore : SecStore :=
  fun _ => SecLabel.trusted

def sqlOnlyThenHtmlSink : List SInstr :=
  [ SInstr.source 0
  , SInstr.sanitize 1 0 SinkKind.sql
  , SInstr.sink 1 SinkKind.html 31
  ]

def htmlSanitizedThenHtmlSink : List SInstr :=
  [ SInstr.source 0
  , SInstr.sanitize 1 0 SinkKind.html
  , SInstr.sink 1 SinkKind.html 31
  ]

def sqlSanitizedThenSqlSink : List SInstr :=
  [ SInstr.source 0
  , SInstr.sanitize 1 0 SinkKind.sql
  , SInstr.sink 1 SinkKind.sql 32
  ]

example : (sexec emptySecStore sqlOnlyThenHtmlSink).2 = [31] := by
  native_decide

example : (sexec emptySecStore htmlSanitizedThenHtmlSink).2 = [] := by
  native_decide

example : (sexec emptySecStore sqlSanitizedThenSqlSink).2 = [] := by
  native_decide

example : 31 ∉ (sexec emptySecStore htmlSanitizedThenHtmlSink).2 :=
  sanitizer_fix_gate
    (SecStore.sound_refl emptySecStore)
    (by native_decide)

theorem wrong_context_sanitizer_does_not_prove_html_safe :
    ¬ (SecLabel.sanitize SecLabel.input SinkKind.sql).safeFor SinkKind.html := by
  intro h
  simp [SecLabel.sanitize, SecLabel.safeFor, SecLabel.input, Protection.add, Protection.has] at h
  cases h

end PcSastLean
