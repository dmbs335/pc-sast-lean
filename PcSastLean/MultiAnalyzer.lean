import PcSastLean.CIGate

/-!
Multi-analyzer aggregation.

Real SAST CI does not run one analysis.  It aggregates taint/heap/framework/CPG
findings into one report.  This module proves the small but important closure
property: if each analyzer family is sound, then their union is sound, and the
top-level no-bug-hiding CI theorem applies to the aggregate run.
-/

namespace PcSastLean

def unionNodes (xs ys : List Node) : List Node :=
  xs ++ ys

def aggregateRuns : List AnalyzerRun -> AnalyzerRun
  | [] => { concrete := [], abstract := [] }
  | r :: rest =>
      let tail := aggregateRuns rest
      { concrete := unionNodes r.concrete tail.concrete
      , abstract := unionNodes r.abstract tail.abstract
      }

theorem subset_append_left {xs ys : List Node} :
    ListSubset xs (xs ++ ys) := by
  intro id h
  exact List.mem_append_left ys h

theorem subset_append_right {xs ys : List Node} :
    ListSubset ys (xs ++ ys) := by
  intro id h
  exact List.mem_append_right xs h

theorem append_subset_append
    {xs₁ xs₂ ys₁ ys₂ : List Node}
    (h₁ : ListSubset xs₁ ys₁)
    (h₂ : ListSubset xs₂ ys₂) :
    ListSubset (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  intro id h
  cases List.mem_append.mp h with
  | inl hx =>
      exact List.mem_append_left ys₂ (h₁ id hx)
  | inr hx =>
      exact List.mem_append_right ys₁ (h₂ id hx)

theorem aggregateRuns_sound
    {runs : List AnalyzerRun}
    (hsound : forall r, r ∈ runs -> r.Sound) :
    (aggregateRuns runs).Sound := by
  induction runs with
  | nil =>
      intro id h
      simp [aggregateRuns] at h
  | cons r rest ih =>
      have hr : r.Sound := hsound r (by simp)
      have htail : (aggregateRuns rest).Sound := by
        apply ih
        intro r' hr'
        exact hsound r' (by simp [hr'])
      unfold AnalyzerRun.Sound
      simp [aggregateRuns, unionNodes]
      exact append_subset_append hr htail

theorem aggregate_ci_gate_no_bug_hiding
    {runs : List AnalyzerRun} {triage : TriageRun}
    (hsound : forall r, r ∈ runs -> r.Sound)
    (hcomplete : triage.Complete (aggregateRuns runs)) :
    ListSubset (aggregateRuns runs).concrete triage.report := by
  exact ci_gate_no_bug_hiding (aggregateRuns_sound hsound) hcomplete

/-! ## Demo -/

def runA : AnalyzerRun := { concrete := [1], abstract := [1, 2] }
def runB : AnalyzerRun := { concrete := [3], abstract := [3] }

theorem runASound : runA.Sound := by
  intro id h
  simp [runA] at h ⊢
  exact Or.inl h

theorem runBSound : runB.Sound := by
  intro id h
  simp [runB] at h ⊢
  exact h

def aggregateDemoTriage : TriageRun :=
  { report := (aggregateRuns [runA, runB]).abstract
  , suppressed := []
  , evidence := []
  }

theorem aggregateDemoComplete :
    aggregateDemoTriage.Complete (aggregateRuns [runA, runB]) := by
  intro sink habs
  left
  exact habs

example :
    ListSubset (aggregateRuns [runA, runB]).concrete aggregateDemoTriage.report :=
  aggregate_ci_gate_no_bug_hiding
    (by
      intro r hr
      have hcases : r = runA ∨ r = runB := by
        simpa using hr
      cases hcases with
      | inl hA =>
          subst hA
          exact runASound
      | inr hB =>
          subst hB
          exact runBSound)
    aggregateDemoComplete

end PcSastLean
