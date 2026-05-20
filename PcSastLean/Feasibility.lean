import PcSastLean.CPGProvenance

/-!
Path feasibility obligations.

SAST false positives often come from infeasible paths.  `SuppressionGate` already
requires a concrete-impossible witness before hiding a finding.  This module adds
a tiny symbolic path-condition language and an unsat witness that can discharge
such suppressions.
-/

namespace PcSastLean

abbrev SymVar := Nat

inductive BoolExpr where
  | lit (b : Bool)
  | var (v : SymVar)
  | not (e : BoolExpr)
  | and (l r : BoolExpr)
  | or (l r : BoolExpr)
deriving DecidableEq, Repr

def BoolExpr.eval (env : SymVar -> Bool) : BoolExpr -> Bool
  | BoolExpr.lit b => b
  | BoolExpr.var v => env v
  | BoolExpr.not e => !(e.eval env)
  | BoolExpr.and l r => l.eval env && r.eval env
  | BoolExpr.or l r => l.eval env || r.eval env

abbrev PathCondition := List BoolExpr

def Satisfies (env : SymVar -> Bool) (pc : List BoolExpr) : Prop :=
  forall e, e ∈ pc -> e.eval env = true

def Feasible (pc : List BoolExpr) : Prop :=
  exists env, Satisfies env pc

structure UnsatWitness where
  pivot : BoolExpr
deriving Repr

def UnsatWitness.Valid (pc : List BoolExpr) (w : UnsatWitness) : Prop :=
  w.pivot ∈ pc /\ BoolExpr.not w.pivot ∈ pc

theorem valid_unsat_witness_implies_infeasible
    {pc : PathCondition} {w : UnsatWitness}
    (h : w.Valid pc) :
    ¬ Feasible pc := by
  intro hfeasible
  rcases hfeasible with ⟨env, hsat⟩
  have hpivot := hsat w.pivot h.left
  have hnot := hsat (BoolExpr.not w.pivot) h.right
  simp [BoolExpr.eval, hpivot] at hnot

def checkUnsatWitness (pc : List BoolExpr) (w : UnsatWitness) : Bool :=
  decide (w.pivot ∈ pc) && decide (BoolExpr.not w.pivot ∈ pc)

theorem checkUnsatWitness_sound
    {pc : PathCondition} {w : UnsatWitness}
    (h : checkUnsatWitness pc w = true) :
    ¬ Feasible pc := by
  simp [checkUnsatWitness, UnsatWitness.Valid] at h
  exact valid_unsat_witness_implies_infeasible (And.intro h.left h.right)

structure FeasibleFinding where
  sink : Node
  pc : List BoolExpr
deriving Repr

def FindingConcretePossible (f : FeasibleFinding) : Prop :=
  Feasible f.pc

theorem unsat_finding_not_concrete_possible
    {f : FeasibleFinding} {w : UnsatWitness}
    (h : checkUnsatWitness f.pc w = true) :
    ¬ FindingConcretePossible f := by
  exact checkUnsatWitness_sound h

def FeasibleSuppressionSound
    (findings : List FeasibleFinding) (suppressed : List Node)
    (witnessOf : Node -> Option UnsatWitness) : Prop :=
  forall f,
    f ∈ findings ->
    f.sink ∈ suppressed ->
    exists w, witnessOf f.sink = some w /\ ¬ FindingConcretePossible f

/-! ## Demo: contradictory branch guards suppress a CPG-like finding -/

def guard : BoolExpr := BoolExpr.var 0

def infeasibleFinding : FeasibleFinding :=
  { sink := 71
  , pc := [guard, BoolExpr.not guard]
  }

def infeasibleWitness : UnsatWitness := { pivot := guard }

example : checkUnsatWitness infeasibleFinding.pc infeasibleWitness = true := by
  native_decide

example : ¬ FindingConcretePossible infeasibleFinding :=
  unsat_finding_not_concrete_possible (w := infeasibleWitness) (by native_decide)

def feasibleSuppressed : List Node := [71]

example :
    FeasibleSuppressionSound [infeasibleFinding] feasibleSuppressed
      (fun id => if id = 71 then some infeasibleWitness else none) := by
  intro f hf hsupp
  have hfEq : f = infeasibleFinding := by
    simpa [infeasibleFinding] using hf
  subst hfEq
  refine ⟨infeasibleWitness, ?_, ?_⟩
  · simp [feasibleSuppressed] at hsupp
    simp [hsupp]
  · exact unsat_finding_not_concrete_possible (w := infeasibleWitness) (by native_decide)

end PcSastLean
