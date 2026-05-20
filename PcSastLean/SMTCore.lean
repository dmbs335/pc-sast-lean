import PcSastLean.Feasibility

/-!
SMT-style unsat core certificates.

`Feasibility.lean` supports a direct contradiction witness: both `p` and
`not p` are in the path condition.  Real solvers usually return an unsat core: a
subset of asserted clauses that is itself inconsistent.

This module models a small checked unsat-core certificate.  The core is a list of
indices into the path condition, and the checker accepts when the selected
clauses contain a direct contradiction.

Claim boundary:

* Verified here: a selected Boolean core containing `p` and `not p` makes the
  path condition infeasible in the toy Boolean semantics.
* External obligations: richer SMT proof formats must justify theory lemmas.
* Not modeled here: LRA, EUF, strings, arrays, regexes, bitvectors, quantifiers,
  or solver proof replay.
-/

namespace PcSastLean

def getCoreClauses (pc : List BoolExpr) (idxs : List Nat) : List BoolExpr :=
  idxs.filterMap (fun i => pc.get? i)

structure UnsatCoreCert where
  indices : List Nat
  pivot : BoolExpr
deriving Repr

def UnsatCoreCert.Valid (pc : List BoolExpr) (cert : UnsatCoreCert) : Prop :=
  cert.pivot ∈ getCoreClauses pc cert.indices /\
  BoolExpr.not cert.pivot ∈ getCoreClauses pc cert.indices /\
  cert.pivot ∈ pc /\
  BoolExpr.not cert.pivot ∈ pc

theorem valid_unsat_core_implies_infeasible
    {pc : List BoolExpr} {cert : UnsatCoreCert}
    (h : cert.Valid pc) :
    ¬ Feasible pc := by
  exact valid_unsat_witness_implies_infeasible
    (w := { pivot := cert.pivot })
    (And.intro h.right.right.left h.right.right.right)

def checkUnsatCore (pc : List BoolExpr) (cert : UnsatCoreCert) : Bool :=
  let core := getCoreClauses pc cert.indices
  decide (cert.pivot ∈ core) &&
  decide (BoolExpr.not cert.pivot ∈ core) &&
  decide (cert.pivot ∈ pc) &&
  decide (BoolExpr.not cert.pivot ∈ pc)

theorem checkUnsatCore_sound
    {pc : List BoolExpr} {cert : UnsatCoreCert}
    (h : checkUnsatCore pc cert = true) :
    ¬ Feasible pc := by
  simp [checkUnsatCore, UnsatCoreCert.Valid] at h
  exact valid_unsat_core_implies_infeasible
    (And.intro h.left.left.left
      (And.intro h.left.left.right
        (And.intro h.left.right h.right)))

theorem unsat_core_finding_not_concrete_possible
    {f : FeasibleFinding} {cert : UnsatCoreCert}
    (h : checkUnsatCore f.pc cert = true) :
    ¬ FindingConcretePossible f := by
  exact checkUnsatCore_sound h

/-! ## Demo -/

def smtCoreFinding : FeasibleFinding :=
  { sink := 81
  , pc := [BoolExpr.var 0, BoolExpr.var 1, BoolExpr.not (BoolExpr.var 0)]
  }

def smtCoreCert : UnsatCoreCert :=
  { indices := [0, 2], pivot := BoolExpr.var 0 }

example : getCoreClauses smtCoreFinding.pc smtCoreCert.indices =
    [BoolExpr.var 0, BoolExpr.not (BoolExpr.var 0)] := by
  native_decide

example : checkUnsatCore smtCoreFinding.pc smtCoreCert = true := by
  native_decide

example : ¬ FindingConcretePossible smtCoreFinding :=
  unsat_core_finding_not_concrete_possible (cert := smtCoreCert) (by native_decide)

end PcSastLean
