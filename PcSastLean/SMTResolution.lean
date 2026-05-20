import PcSastLean.SMTCore

/-!
Resolution-chain feasibility certificates.

`SMTCore` checks only a direct Boolean contradiction.  This module adds a small
propositional proof-step language: a unit literal can be propagated through a
chain of implication clauses `¬p ∨ q`, eventually contradicting a final negative
unit.  This is still far from production SMT proof replay, but it is no longer
just a hard-coded `p` / `not p` pivot.

Claim boundary:

* Verified here: accepted propositional implication-chain certificates make the
  toy Boolean path condition infeasible.
* External obligations: theory lemmas from LRA, EUF, strings, arrays, regexes,
  and bitvectors must still be supplied by richer proof checkers.
* Not modeled here: CDCL proof formats, clause learning, resolution DAGs,
  quantifiers, or solver-specific proof replay.
-/

namespace PcSastLean

structure PropLit where
  atom : SymVar
  positive : Bool
deriving DecidableEq, Repr

def PropLit.negate (l : PropLit) : PropLit :=
  { l with positive := !l.positive }

def PropLit.eval (env : SymVar -> Bool) (l : PropLit) : Bool :=
  if l.positive then env l.atom else !(env l.atom)

def PropLit.toExpr (l : PropLit) : BoolExpr :=
  if l.positive then BoolExpr.var l.atom else BoolExpr.not (BoolExpr.var l.atom)

theorem propLit_toExpr_eval (env : SymVar -> Bool) (l : PropLit) :
    l.toExpr.eval env = l.eval env := by
  cases l with
  | mk atom positive =>
      cases positive <;> simp [PropLit.toExpr, PropLit.eval, BoolExpr.eval]

theorem propLit_negate_eval (env : SymVar -> Bool) (l : PropLit) :
    l.negate.eval env = !(l.eval env) := by
  cases l with
  | mk atom positive =>
      cases positive <;> simp [PropLit.negate, PropLit.eval]

def implicationExpr (premise conclusion : PropLit) : BoolExpr :=
  BoolExpr.or premise.negate.toExpr conclusion.toExpr

def lastLit : PropLit -> List PropLit -> PropLit
  | current, [] => current
  | _current, next :: rest => lastLit next rest

def checkImplicationChain
    (pc : PathCondition) : PropLit -> List PropLit -> Bool
  | _current, [] => true
  | current, next :: rest =>
      decide (implicationExpr current next ∈ pc) &&
      checkImplicationChain pc next rest

theorem implicationExpr_sound
    {pc : PathCondition} {env : SymVar -> Bool}
    {premise conclusion : PropLit}
    (hsat : Satisfies env pc)
    (hmem : implicationExpr premise conclusion ∈ pc)
    (hpremise : premise.eval env = true) :
    conclusion.eval env = true := by
  have hclause := hsat (implicationExpr premise conclusion) hmem
  simp [implicationExpr, BoolExpr.eval, propLit_toExpr_eval,
    propLit_negate_eval, hpremise] at hclause
  exact hclause

theorem checked_implication_chain_sound
    {pc : PathCondition} {env : SymVar -> Bool}
    (hsat : Satisfies env pc) :
    forall chain current,
      checkImplicationChain pc current chain = true ->
      current.eval env = true ->
      (lastLit current chain).eval env = true := by
  intro chain
  induction chain with
  | nil =>
      intro current _ hcurrent
      exact hcurrent
  | cons next rest ih =>
      intro current hcheck hcurrent
      simp [checkImplicationChain] at hcheck
      have hnext := implicationExpr_sound hsat hcheck.left hcurrent
      exact ih next hcheck.right hnext

structure ResolutionChainCert where
  start : PropLit
  chain : List PropLit
deriving Repr

def ResolutionChainCert.finalLit (cert : ResolutionChainCert) : PropLit :=
  lastLit cert.start cert.chain

def checkResolutionChainUnsat
    (pc : PathCondition) (cert : ResolutionChainCert) : Bool :=
  decide (cert.start.toExpr ∈ pc) &&
  checkImplicationChain pc cert.start cert.chain &&
  decide (cert.finalLit.negate.toExpr ∈ pc)

theorem checkResolutionChainUnsat_sound
    {pc : PathCondition} {cert : ResolutionChainCert}
    (hcheck : checkResolutionChainUnsat pc cert = true) :
    ¬ Feasible pc := by
  intro hfeasible
  rcases hfeasible with ⟨env, hsat⟩
  simp [checkResolutionChainUnsat] at hcheck
  have hstartExpr := hsat cert.start.toExpr hcheck.left.left
  have hstart : cert.start.eval env = true := by
    simpa [propLit_toExpr_eval] using hstartExpr
  have hfinal := checked_implication_chain_sound hsat
    cert.chain cert.start hcheck.left.right hstart
  have hnegExpr := hsat cert.finalLit.negate.toExpr hcheck.right
  have hneg : cert.finalLit.negate.eval env = true := by
    simpa [propLit_toExpr_eval] using hnegExpr
  have hfinalCert : cert.finalLit.eval env = true := by
    simpa [ResolutionChainCert.finalLit] using hfinal
  simp [propLit_negate_eval, hfinalCert] at hneg

theorem resolution_chain_finding_not_concrete_possible
    {f : FeasibleFinding} {cert : ResolutionChainCert}
    (h : checkResolutionChainUnsat f.pc cert = true) :
    ¬ FindingConcretePossible f := by
  exact checkResolutionChainUnsat_sound h

/-! ## Demo -/

def litP : PropLit := { atom := 0, positive := true }
def litQ : PropLit := { atom := 1, positive := true }

def resolutionFinding : FeasibleFinding :=
  { sink := 111
  , pc :=
      [ litP.toExpr
      , implicationExpr litP litQ
      , litQ.negate.toExpr
      ]
  }

def resolutionCert : ResolutionChainCert :=
  { start := litP, chain := [litQ] }

example : checkResolutionChainUnsat resolutionFinding.pc resolutionCert = true := by
  native_decide

example : ¬ FindingConcretePossible resolutionFinding :=
  resolution_chain_finding_not_concrete_possible
    (cert := resolutionCert)
    (by native_decide)

end PcSastLean
