import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle

open MeasureTheory Filter Metric Function
open scoped omegaLimit
set_option autoImplicit false

/- For every objective, first write down a statement that Lean understands, with a proof given
by `sorry`. Then try to prove it! -/

section Topological_Dynamics

/- We could do everything in a topological space, using filters and neighborhoods, but it will
be more comfortable with a metric space. -/
variable {α : Type _} [MetricSpace α]

/- Define the non-wandering set of `f`-/
def nonWanderingSet (f : α → α) : Set α :=
  {x | ∀ ε, 0 < ε → ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ n ≠ 0}

variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/- Show that periodic points belong to the non-wandering set -/
theorem Function.IsPeriodicPt.mem_nonWanderingSet
    (x : α) (n : ℕ) (hn : n ≠ 0) (hf : IsPeriodicPt f n x) :
    x ∈ nonWanderingSet f := by
  refine' fun ε εpos ↦ ⟨x, n, mem_ball_self εpos, _, hn⟩
  rw [hf]
  exact mem_ball_self εpos

/- Show that, if `x` belongs to the non-wandering set, there are points `y` arbitrarily close to `x`
and arbitrarily large times for which `f^[n] y` comes back close to `x`. -/
theorem exists_large_times_of_mem_nonWanderingSet (x : α) (hx : x ∈ nonWanderingSet f) (N : ℕ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ y n, y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ N < n := by
  sorry

/- Show that the non-wandering set of `f` is closed. -/

theorem zou : IsClosed (nonWanderingSet f) := by
  rw [← isSeqClosed_iff_isClosed]
  intros u x hu u_lim
  rw [tendsto_atTop_nhds] at u_lim

/- Show that the non-wandering set of `f` is compact. -/


/- Show that the omega-limit set of any point is nonempty. -/
/- Click F12 on ω⁺ below to go to its definition, and browse a little bit the file to get a
feel of what is already there. -/
theorem omegaLimit_nonempty (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) := by
  sorry

/- Show that the omega-limit set of any point is contained in the non-wandering set. -/


/- Show that the non-wandering set is non-empty -/


/- Define the recurrent set of `f`. -/
def recurrentSet {α : Type _} [TopologicalSpace α] (f : α → α) : Set α := sorry

/- Show that periodic points belong to the recurrent set. -/


/- Show that the recurrent set is included in the non-wandering set -/


/- Show that the recurrent set of `f` is nonempty (the math proof is not trivial, maybe better
skip this one). -/


end Topological_Dynamics




section Ergodic_Theory

/- standing assumptions: `f` is a measure preserving map of a probability space `(α, μ)`, and
`g : α → ℝ` is integrable. -/

variable {α : Type _} [MetricSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : MeasureTheory.Measure α} [IsProbabilityMeasure μ] {f : α → α}
  (hf : MeasurePreserving f μ) {g : α → ℝ} (hg : Integrable g μ)


/- Define Birkhoff sums. -/
def birkhoffSum {α : Type _} (f : α → α) (g : α → ℝ) (n : ℕ) (x : α) : ℝ := sorry


/- Define the invariant sigma-algebra of `f` -/



/- Main lemma to prove Birkhoff ergodic theorem:
assume that the integral of `g` on any invariant set is strictly negative. Then, almost everywhere,
the Birkhoff sums `S_n g x` are bounded above.
-/


/- Deduce Birkhoff theorem from the main lemma, in the form that almost surely, `S_n f / n`
converges to the conditional expectation of `f` given the invariant sigma-algebra. -/


/- If `f` is ergodic, show that the invariant sigma-algebra is ae trivial -/


/- Show that the conditional expectation with respect to an ae trivial subalgebra is ae
the integral. -/


/- Give Birkhoff theorem for ergodic maps -/


end Ergodic_Theory
