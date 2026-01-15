/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The midpoint rule

This file contains a definition of integration on `[[a, b]]` via the midpoint rule, along with
an error bound in terms of a bound on the second derivative of the integrand.

## Main results
- `midpoint_error_le`: the convergence theorem for the midpoint rule.

## References
We follow the proof on (Wikipedia)[https://en.wikipedia.org/wiki/Trapezoidal_rule] for the error
bound.
-/

@[expose] public section

open MeasureTheory Set Finset intervalIntegral Interval

/-- Integration of `f` from `a` to `b` using the midpoint rule with `N+1` total evaluations of
`f`.  (Note the off-by-one problem here: `N` counts the number of trapezoids, not the number of
evaluations.) -/
noncomputable def midpoint_integral (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ((b - a) / N) * (∑ k ∈ range N, f (a + (k + 1/2) * (b - a) / N))

/-- The absolute error of midpoint integration. -/
noncomputable def midpoint_error (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  (midpoint_integral f N a b) - (∫ x in a..b, f x)

theorem midpoint_integral_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    midpoint_integral f N a b = -(midpoint_integral f N b a) := by
  unfold midpoint_integral
  rw [neg_mul_eq_neg_mul, neg_div', neg_sub, ← sum_range_reflect]
  congr 1
  apply sum_congr rfl
  intro k hk
  congr 1
  rw [tsub_tsub, add_comm 1, Nat.cast_sub (mem_range.mp hk)]
  simpa [field] using by ring

/-- The absolute error of the midpoint rule does not change when the endpoints are swapped. -/
theorem midpoint_error_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    midpoint_error f N a b = -midpoint_error f N b a := by
  unfold midpoint_error
  rw [midpoint_integral_symm f N_nonzero a b, neg_sub', integral_symm]

/-- Just like exact integration, the midpoint integration from `a` to `a` is zero. -/
@[simp]
theorem midpoint_integral_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) : midpoint_integral f N a a = 0 := by
  simp [midpoint_integral]

/-- The error of the midpoint integration from `a` to `a` is zero. -/
@[simp]
theorem midpoint_error_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) : midpoint_error f N a a = 0 := by
  simp [midpoint_error]

/-- An exact formula for integration with a single midpoint (the "midpoint rule"). -/
@[simp]
theorem midpoint_integral_one (f : ℝ → ℝ) (a b : ℝ) :
    midpoint_integral f 1 a b = (b - a) * (f ((a + b) / 2)) := by
  simpa [midpoint_integral] using by left; ring_nf

/-- A basic midpoint equivalent to `IntervalIntegral.sum_integral_adjacent_intervals`. More
general theorems are certainly possible, but many of them can be derived from repeated applications
of this one. -/
theorem sum_midpoint_integral_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ}
    (N_nonzero : 0 < N) : ∑ i ∈ range N, midpoint_integral f 1 (a + i * h) (a + (i + 1) * h)
      = midpoint_integral f N a (a + N * h) := by
  simp_rw [midpoint_integral_one, add_sub_add_left_eq_sub, ← sub_mul, midpoint_integral,
    add_sub_cancel_left, one_mul, ← mul_sum, ← mul_div, show N * (h / N) = h by field]
  ring_nf

/-- A simplified version of the previous theorem, for use in proofs by induction and the like. -/
theorem midpoint_integral_ext {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : 0 < N) :
    midpoint_integral f N a (a + N * h) + midpoint_integral f 1 (a + N * h) (a + (N + 1) * h)
      = midpoint_integral f (N + 1) a (a + (N + 1) * h) := by
  rw [← Nat.cast_add_one, ← sum_midpoint_integral_adjacent_intervals N_nonzero,
      ← sum_midpoint_integral_adjacent_intervals (Nat.add_pos_left N_nonzero 1),
      sum_range_succ, Nat.cast_add_one]

/-- Since we have `sum_[]_adjacent_intervals` theorems for both exact and midpoint integration,
it's natural to combine them into a similar formula for the error.  This theorem is in particular
used in the proof of the general error bound. -/
theorem sum_midpoint_error_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : 0 < N)
    (h_f_int : IntervalIntegrable f volume a (a + N * h)) :
    ∑ i ∈ range N, midpoint_error f 1 (a + i * h) (a + (i + 1) * h)
      = midpoint_error f N a (a + N * h) := by
  unfold midpoint_error
  rw [sum_sub_distrib, sum_midpoint_integral_adjacent_intervals N_nonzero]
  norm_cast
  rw [sum_integral_adjacent_intervals]
  · simp
  · intro k hk
    suffices ∀ {k : ℕ}, k ≤ N → a + k * h ∈ [[a, a + N * h]] from
      IntervalIntegrable.mono h_f_int (Set.uIcc_subset_uIcc (this hk.le) (this hk)) le_rfl
    rcases le_total h 0 with h_neg | h_pos <;> intro k hk <;> rw [← Nat.cast_le (α := ℝ)] at hk
    · simpa [Set.mem_uIcc] using .inr
        ⟨mul_le_mul_of_nonpos_right hk h_neg, mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg h_neg⟩
    · exact Set.mem_uIcc_of_le (le_add_of_nonneg_right (by positivity)) (by grw [hk])

lemma useful {F : ℝ → ℝ} {h : ℝ} (x : ℝ) (hh : 0 < h) (hF : ContDiffOn ℝ 3 F (Icc x (x + h)))
    (hx : ContDiffAt ℝ 2 F x) : ∃ ξ1 ∈ Ioo x (x + h), F (x + h) - (F x + h * deriv F x +
    1 / 2 * h ^ 2 * iteratedDeriv 2 F x) = iteratedDeriv 3 F ξ1 * h ^ 3 / 6 := by
  have hm : x < x + h := by simpa using (half_lt_self hh)
  have hm_mem : x ∈ Icc x (x + h) := ⟨le_rfl, le_of_lt hm⟩
  have hUD : UniqueDiffOn ℝ (Icc x (x + h)) := uniqueDiffOn_Icc hm
  obtain ⟨ξ1, hξ1, hξ1_rem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (f := F) hm (by fun_prop)
  norm_num [sub_half] at hξ1_rem
  refine ⟨ξ1, hξ1, ?_⟩
  simp only [one_div, ← hξ1_rem, sub_right_inj]
  congr
  · refine Eq.symm (DifferentiableAt.derivWithin ?_ (hUD x hm_mem))
    exact hx.differentiableAt (by norm_num)
  · exact Eq.symm (iteratedDerivWithin_eq_iteratedDeriv hUD hx hm_mem)

theorem midpoint_aux {F : ℝ → ℝ} {h : ℝ} (hh : 0 < h) (hF : ContDiff ℝ 3 F) :
    ∃ ξ ∈ Ioo (0 : ℝ) h, F h - F 0 - (deriv F (h/2)) * h = (h^3 / 24) * (iteratedDeriv 3 F ξ) := by
  obtain ⟨ξ1, hξ1, hξ1_rem⟩ := useful (h/2) (half_pos hh) (F := F) (by fun_prop) (by
    have hcdW2 : ContDiff ℝ 2 F := by fun_prop
    fun_prop)
  have : ContDiff ℝ 2 (fun x ↦ F (h - x)) := by fun_prop
  obtain ⟨ζ, hζ, hζ_rem⟩ := useful (F := fun x => F (h - x)) (h/2) (half_pos hh) (by fun_prop)
    this.contDiffAt
  obtain ⟨ξ, hξ_mem, hy⟩ : (iteratedDeriv 3 F ξ1 + iteratedDeriv 3 F (h - ζ)) / 2 ∈
      (iteratedDeriv 3 F) '' (uIcc ξ1 (h - ζ)) :=
    intermediate_value_uIcc (hF.continuous_iteratedDeriv' 3).continuousOn (by grind [Set.mem_uIcc])
  norm_num [-one_div, sub_half] at hξ1 hζ hξ1_rem hζ_rem
  have hξ0h : ξ ∈ Ioo (0:ℝ) h := by
    have : ξ ∈ Icc (min ξ1 (h - ζ)) (max ξ1 (h - ζ)) := by simpa [Set.uIcc] using hξ_mem
    constructor
    · have lt : 0 < min ξ1 (h - ζ) := by simp [(half_pos hh).trans hξ1.1, hζ]
      linarith [this.1]
    · have lt : max ξ1 (h - ζ) < h := by simp [(half_pos hh).trans hζ.1, hξ1]
      linarith [this.2]
  refine ⟨ξ, hξ0h, ?_⟩
  calc
  _ = F h - (F (h/2) + h / 2 * deriv F (h/2) + 1 / 2 * (h/2) ^ 2 * iteratedDeriv 2 F (h/2))
      - (F 0 - (F (h/2) + h/2 * deriv (fun x ↦ F (h - x)) (h/2) +
      1 / 2 * (h/2) ^ 2 * iteratedDeriv 2 (fun x ↦ F (h - x)) (h/2))) := by
    simp [iteratedDeriv_comp_const_sub, deriv_comp_const_sub, sub_half, field]
    ring
  _ = h ^ 3 / 48 * iteratedDeriv 3 F ξ1 + h ^ 3 / 48 * iteratedDeriv 3 F (h - ζ) := by
    rw [hξ1_rem, hζ_rem]
    simpa [field, mul_assoc, iteratedDeriv_comp_const_sub] using by norm_num
  _ = _ := by grind

theorem midpoint_rule_error {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContDiff ℝ 2 f) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - f ((a + b) / 2) * (b - a)
      = (b - a)^3 / 24 * (iteratedDeriv 2 f ξ) := by
  set h : ℝ := b - a with hdef
  set g : ℝ → ℝ := fun x => f (x + a) with gdef
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
  have hg : ContDiff ℝ 2 g := by fun_prop
  have hFderiv : deriv F = g := by
    funext x
    simpa [F] using hg.continuous.deriv_integral g 0 x
  have hFcont : ContDiff ℝ 3 F := (contDiff_succ_iff_deriv (n := 2) (f₂ := F)).2
      ⟨intervalIntegral.differentiable_integral_of_continuous hg.continuous, by simp,
      by simpa [hFderiv] using hg⟩
  rcases midpoint_aux (F := F) (sub_pos.mpr hab) hFcont with ⟨ξ0, hξ0, hEq⟩
  refine ⟨a + ξ0, by grind, ?_⟩
  have hDerivMid : deriv F (h / 2) = f ((a + b) / 2) := by
    simp [hFderiv, g, add_comm, hdef]
    ring_nf
  have hIter3 : iteratedDeriv 3 F ξ0 = iteratedDeriv 2 f (a + ξ0) := by calc
    _ = iteratedDeriv 2 (deriv F) ξ0 := congrArg (fun u ↦ u ξ0) iteratedDeriv_succ'
    _ = _ := by rw [hFderiv, gdef, iteratedDeriv_comp_add_const, add_comm]
  have hEq' : F h - deriv F (h / 2) * h = (h^3 / 24) * iteratedDeriv 3 F ξ0 := by
    simpa [F] using hEq
  have hFh : F h = (∫ x in a..b, f x) := by simp [F, g, h, add_comm]
  simpa only [hFh, hDerivMid, hIter3] using hEq'
