import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle

open MeasureTheory Filter Metric Function
open scoped omegaLimit
set_option autoImplicit false

set_option autoImplicit false

/- For every objective, first write down a statement that Lean understands, with a proof given
by `sorry`. Then try to prove it! -/

section Topological_Dynamics

/- TODO: at some point translate to topological spaces -/

/- We could do everything in a topological space, using filters and neighborhoods, but it will
be more comfortable with a metric space. -/
variable {α : Type _} [MetricSpace α]

/- Define the non-wandering set of `f`-/
def nonWanderingSet (f : α → α) : Set α :=
  {x | ∀ ε, 0 < ε → ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ n ≠ 0}

variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/- Show that periodic points belong to the non-wandering set -/
theorem periodicpts_is_mem (x : α) (n : ℕ) (nnz: n ≠ 0) (pp: IsPeriodicPt f n x) :
    x ∈ nonWanderingSet f := by
  intro ε hε
  use x, n
  -- unfold IsPeriodicPt at pp
  -- unfold IsFixedPt at pp
  refine' ⟨_, _, _⟩
  . exact mem_ball_self hε
  . rw [pp]
    exact mem_ball_self hε
  . exact nnz
  done

/- Show that, if `x` belongs to the non-wandering set, there are points `y` arbitrarily close to `x`
and arbitrarily large times for which `f^[n] y` comes back close to `x`. -/
theorem arbitrary_return
    (x : α) (hx: x ∈ nonWanderingSet f) (N : ℕ) (hN: N ≠ 0) (ε : ℝ) (hε: 0 < ε) :
    ∃ z : α, ∃ n : ℕ, n > N ∧ z ∈ ball x ε ∧ (f^[n] z) ∈ ball x ε := by
  unfold nonWanderingSet at hx
  sorry

/- Show that the non-wandering set of `f` is closed. -/
theorem is_closed : IsClosed (nonWanderingSet f : Set α) := by
  rw [← isSeqClosed_iff_isClosed]
  unfold IsSeqClosed
  intro u x hu ulim
  rw [tendsto_atTop_nhds] at ulim
  intro ε hepos
  have e2pos : 0 < ε / 2 := by
    linarith
  have h1 : IsOpen (ball x (ε / 2)) := by
    exact isOpen_ball
  have h2 : ∃ (z : α), z ∈ ball x (ε/ 2) ∧ z ∈ nonWanderingSet f := by
    let k1 := ulim (ball x (ε / 2))
    have k2 : x ∈ (ball x (ε / 2)) := by
      exact mem_ball_self e2pos
    let ⟨N, k3⟩ := k1 k2 h1
    have k4 : u N ∈ ball x (ε / 2) := by
      have k5 : N ≤ N := by
        exact Nat.le_refl N
      exact k3 N k5 -- it seems not to be necessary??
    exact ⟨u N, k4, hu N⟩
  rcases h2 with ⟨z, h3, h4⟩
  have h5 : ∃ (y : α), ∃ (n : ℕ), y ∈ ball z (ε / 2) ∧ f^[n] y ∈ ball z (ε / 2) ∧ n ≠ 0 := by
    simp [nonWanderingSet] at h4
    let l1 := h4 (ε / 2) e2pos
    rcases l1 with ⟨y, l1, ⟨n, l2, l3⟩⟩
    use y, n -- note 'use y, n' which is the same as 'use y' and 'use n'
    simp
    exact ⟨l1, l2, l3⟩
  rcases h5 with ⟨y, n, h6, h7, h8⟩
  have h9 : y ∈ ball x ε := by
    simp
    have m1 : dist y z + dist z x < ε := by
      rw [mem_ball] at h3 h6
      linarith
    have : dist y x ≤ dist y z + dist z x := by
      exact dist_triangle _ _ _  -- why can I omit argument, but I can't in the line below?
    exact lt_of_le_of_lt this m1
  have h10 : f^[n] y ∈ ball x ε := by
    simp
    have p1 : dist (f^[n] y) z + dist z x < ε := by
      rw [mem_ball] at h7 h3
      linarith
    have : dist (f^[n] y) x ≤ dist (f^[n] y) z + dist z x := by
      exact dist_triangle _ _ _  -- why can I omit argument, but I can't in the line below?
    exact lt_of_le_of_lt this p1
  exact ⟨y, n, h9, h10, h8⟩
  done

theorem zou : IsClosed (nonWanderingSet f) := by
  rw [← isSeqClosed_iff_isClosed]
  intros u x hu u_lim
  rw [tendsto_atTop_nhds] at u_lim

/- Show that the non-wandering set of `f` is compact. -/
theorem is_cpt : IsCompact (nonWanderingSet f : Set α) := by
  apply isCompact_of_isClosed_bounded
  . exact is_closed f
  . exact bounded_of_compactSpace
  done

/- Show that the omega-limit set of any point is nonempty. -/
/- Click F12 on ω⁺ below to go to its definition, and browse a little bit the file to get a
feel of what is already there. -/
theorem omegaLimit_nonempty (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) := by
  apply nonempty_omegaLimit atTop (fun n ↦ f^[n]) {x}
  exact Set.singleton_nonempty x
  done

/- Show that the omega-limit set of any point is contained in the non-wandering set. -/
theorem omegaLimit_nonwandering (x : α) : (ω⁺ (fun n ↦ f^[n]) ({x})) ⊆ (nonWanderingSet f) := by
  intro z hz
  rewrite [mem_omegaLimit_iff_frequently] at hz
  simp at hz
  have subsequence : ∀ U ∈ nhds z, ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), f^[φ n] x ∈ U := by
    intro U hU
    apply Filter.extraction_of_frequently_atTop (hz U hU)
    done
  -- unfold nonWanderingSet
  intro ε hε
  have ball_in_nbd : ball z ε ∈ nhds z := by
    exact ball_mem_nhds z hε
  let ⟨φ, hφ, hf⟩ := subsequence (ball z ε) ball_in_nbd
  use f^[φ 1] x, φ 2 - φ 1
  refine' ⟨_, _, _⟩
  . exact (hf 1)
  . have : f^[φ 2 - φ 1] (f^[φ 1] x) = f^[φ 2] x := by
      rw [ <-Function.iterate_add_apply, Nat.sub_add_cancel ]
      apply le_of_lt
      apply hφ
      group
    rw [this]
    apply (hf 2)
  . simp
    apply hφ
    norm_num
  done

/- Show that the non-wandering set is non-empty -/
theorem nonWandering_nonempty [hα : Nonempty α] : Set.Nonempty (nonWanderingSet f) := by
  -- have (A: Set α) (B: Set α) : A ⊆ B -> Set.Nonempty A -> Set.Nonempty B := by
  --   exact fun a a_1 ↦ Set.Nonempty.mono a a_1
  have (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) -> Set.Nonempty (nonWanderingSet f) := by
    apply Set.Nonempty.mono
    apply omegaLimit_nonwandering
  apply this
  apply omegaLimit_nonempty f
  -- Can we avoid using the axiom of choice here?
  apply Nonempty.some hα
  done


/- Define the recurrent set of `f`. The recurrent set is the set of points that are recurrent,
   i.e. that belong to their omega-limit set. -/
def recurrentSet {α : Type _} [TopologicalSpace α] (f : α → α) : Set α :=
  { x | x ∈ ω⁺ (fun n ↦ f^[n]) ({x}) }

/- Show that periodic points belong to the recurrent set. -/
theorem periodicpts_mem_recurrentSet
    (x : α) (n : ℕ) (nnz: n ≠ 0) (hx: IsPeriodicPt f n x)
    : x ∈ recurrentSet f := by
  -- unfold IsPeriodicPt at hx
  -- unfold IsFixedPt at hx
  -- unfold recurrentSet
  have : x ∈ ω⁺ (fun n ↦ f^[n]) ({x} : Set α) := by
    rw [mem_omegaLimit_iff_frequently]
    intro U hU
    simp [frequently_atTop]
    intro a
    have hb : ∃ b, a ≤ b ∧ f^[b] x ∈ U := by
      use a * n
      constructor
      . exact Nat.le_mul_of_pos_right (Nat.pos_of_ne_zero nnz)
      . have : f^[a * n] x = x := by
          exact Function.IsPeriodicPt.const_mul hx a
        rw [this]
        exact mem_of_mem_nhds hU
        done
      done
    apply hb
  apply this
  done

/- Show that the recurrent set is included in the non-wandering set -/
theorem recurrentSet_nonwandering : recurrentSet f ⊆ (nonWanderingSet f) := by
  intro z hz
  unfold recurrentSet at hz
  simp at hz
  apply omegaLimit_nonwandering
  apply hz
  done

/- Define a minimal dynamics (all orbits are dense) -/


/- Show that in a minimal dynamics, the recurrent set is all the space -/


/- Give an example of a continuous dynamics on a compact space in which the recurrent set is all
the space, but the dynamics is not minimal -/

/- Define minimal subsets for `f`, as closed invariant subsets in which all orbits are dense -/


/- Show that every point in a minimal subset is recurrent -/


/- Show that every invariant nonempty closed subset contains at least a minimal invariant subset,
using Zorn lemma. -/



/- Show that the recurrent set of `f` is nonempty -/





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
