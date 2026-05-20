/-!
PC-SAST: a small proof-carrying SAST core.

This file is intentionally tiny.  It models the verification layer we want from
Lean: an external SAST engine may be fast, heuristic, or "soundy", but any result
that crosses the trust boundary must come with a certificate checked here.
-/

namespace PcSastLean

abbrev Var := Nat
abbrev Node := Nat

/-! ## Abstract taint facts -/

structure ConcreteState where
  tainted : Var -> Prop

structure AbsState where
  maybeTainted : Var -> Prop

def SoundState (c : ConcreteState) (a : AbsState) : Prop :=
  forall v, c.tainted v -> a.maybeTainted v

inductive Expr where
  | input : Expr
  | var : Var -> Expr
  | const : Int -> Expr
  | join : Expr -> Expr -> Expr
deriving Repr

def concreteTainted (c : ConcreteState) : Expr -> Prop
  | Expr.input => True
  | Expr.var v => c.tainted v
  | Expr.const _ => False
  | Expr.join l r => concreteTainted c l \/ concreteTainted c r

def abstractTainted (a : AbsState) : Expr -> Prop
  | Expr.input => True
  | Expr.var v => a.maybeTainted v
  | Expr.const _ => False
  | Expr.join l r => abstractTainted a l \/ abstractTainted a r

theorem expr_taint_sound
    {c : ConcreteState} {a : AbsState} {e : Expr}
    (hs : SoundState c a) :
    concreteTainted c e -> abstractTainted a e := by
  induction e with
  | input =>
      intro _
      trivial
  | var v =>
      intro h
      exact hs v h
  | const _ =>
      intro h
      cases h
  | join l r ihl ihr =>
      intro h
      cases h with
      | inl hl => exact Or.inl (ihl hl)
      | inr hr => exact Or.inr (ihr hr)

/-! ## Source-to-sink path certificates -/

structure Edge where
  src : Node
  dst : Node
deriving DecidableEq, Repr

inductive PathOK (g : List Edge) : List Node -> Prop
  | single (n : Node) : PathOK g [n]
  | cons {a b : Node} {rest : List Node} :
      { src := a, dst := b } ∈ g ->
      PathOK g (b :: rest) ->
      PathOK g (a :: b :: rest)

def checkEdge (g : List Edge) (a b : Node) : Bool :=
  decide ({ src := a, dst := b } ∈ g)

def checkPath (g : List Edge) : List Node -> Bool
  | [] => false
  | [_] => true
  | a :: b :: rest => checkEdge g a b && checkPath g (b :: rest)

theorem checkEdge_sound
    {g : List Edge} {a b : Node}
    (h : checkEdge g a b = true) :
    { src := a, dst := b } ∈ g := by
  unfold checkEdge at h
  exact of_decide_eq_true h

theorem checkPath_sound
    {g : List Edge} :
    forall p, checkPath g p = true -> PathOK g p := by
  intro p
  induction p with
  | nil =>
      simp [checkPath]
  | cons a tail ih =>
      cases tail with
      | nil =>
          intro _
          exact PathOK.single a
      | cons b rest =>
          intro h
          simp [checkPath] at h
          exact PathOK.cons (checkEdge_sound h.left) (ih h.right)

structure TaintFindingCert where
  source : Node
  sink : Node
  middle : List Node
deriving Repr

def TaintFindingCert.fullPath (c : TaintFindingCert) : List Node :=
  c.source :: c.middle ++ [c.sink]

structure Policy where
  sources : List Node
  sinks : List Node
deriving Repr

def checkFinding (g : List Edge) (p : Policy) (c : TaintFindingCert) : Bool :=
  decide (c.source ∈ p.sources) &&
  decide (c.sink ∈ p.sinks) &&
  checkPath g c.fullPath

def PolicyViolation (g : List Edge) (p : Policy) : Prop :=
  exists c : TaintFindingCert,
    c.source ∈ p.sources /\
    c.sink ∈ p.sinks /\
    PathOK g c.fullPath

theorem checkFinding_sound
    {g : List Edge} {p : Policy} {c : TaintFindingCert}
    (h : checkFinding g p c = true) :
    c.source ∈ p.sources /\
    c.sink ∈ p.sinks /\
    PathOK g c.fullPath := by
  simp [checkFinding] at h
  exact And.intro h.left.left (And.intro h.left.right (checkPath_sound c.fullPath h.right))

theorem accepted_finding_is_violation
    {g : List Edge} {p : Policy} {c : TaintFindingCert}
    (h : checkFinding g p c = true) :
    PolicyViolation g p := by
  exact Exists.intro c (checkFinding_sound h)

def demoGraph : List Edge :=
  [{ src := 0, dst := 1 }, { src := 1, dst := 2 }]

def demoPolicy : Policy :=
  { sources := [0], sinks := [2] }

def demoCert : TaintFindingCert :=
  { source := 0, sink := 2, middle := [1] }

example : checkFinding demoGraph demoPolicy demoCert = true := by
  native_decide

end PcSastLean
