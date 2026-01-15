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

lemma useful {F : ℝ → ℝ} {a b : ℝ} (hh : a < b)
    (hf : ContDiffOn ℝ 2 F (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc a b)) (Ioo a b)) :
    ∃ ξ1 ∈ Ioo a b, F b - (F a + (b - a) * derivWithin F (Icc a b) a +
    1 / 2 * (b - a) ^ 2 * iteratedDerivWithin 2 F (Icc a b) a)
    = iteratedDerivWithin 3 F (Icc a b) ξ1 * (b - a) ^ 3 / 6 := by
  have hm_mem : a ∈ Icc a b := ⟨le_rfl, Std.le_of_lt hh⟩
  have hUD : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hh
  obtain ⟨ξ1, hξ1, hξ1_rem⟩ := taylor_mean_remainder_lagrange (n := 2) (f := F) hh hf hf'
  norm_num [sub_half] at hξ1_rem
  refine ⟨ξ1, hξ1, ?_⟩
  linarith

open scoped Topology

open Filter

theorem midpoint_aux {F : ℝ → ℝ} {h M : ℝ} (hh : 0 < h)
    (hf : ContDiffOn ℝ 2 F (Icc 0 h))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc 0 h)) (Ioo 0 h))
    (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc 0 h) x| ≤ M) :
    |F h - F 0 - (derivWithin F (Icc 0 h) (h/2)) * h| ≤ (h^3 / 24) * M := by
  have h1 : h/2 < h := by linarith
  have h2 : 0 < h/2 := by linarith
  have t1 : ContDiffOn ℝ 2 F (Icc (h/2) h) := hf.mono (by grind)
  have t2' : ContDiffOn ℝ 2 (fun x ↦ F (h - x)) (Set.Icc 0 h) := by
    have h_mapsTo : Set.MapsTo (fun x : ℝ ↦ h - x) (Set.Icc 0 h) (Set.Icc 0 h) := by
      intro x hx
      simp at hx
      simpa using ⟨by linarith, by linarith⟩
    exact hf.comp (contDiff_const.sub contDiff_id).contDiffOn h_mapsTo
  have t2 : ContDiffOn ℝ 2 (fun x ↦ F (h - x)) (Set.Icc (h / 2) h) := t2'.mono (by grind)
  have eq2 {y : ℝ} (hy : y ∈ Icc (h/2) h) {φ : ℝ → ℝ} (m : ℕ) (hm : ContDiffAt ℝ m φ y):
    iteratedDerivWithin m φ (Icc (h / 2) h) y = iteratedDerivWithin m φ (Set.Icc 0 h) y := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hh) hm (by grind),
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h1) hm (by grind)]
  have hf1' {φ : ℝ → ℝ} (m : ℕ) (hφ : ContDiffOn ℝ m φ (Icc 0 h))
      (hφ' : DifferentiableOn ℝ (iteratedDerivWithin m φ (Icc 0 h)) (Ioo 0 h)) :
      DifferentiableOn ℝ (iteratedDerivWithin m φ (Icc (h/2) h)) (Ioo (h/2) h) := by
    have hd : DifferentiableOn ℝ (iteratedDerivWithin m φ (Set.Icc 0 h)) (Set.Ioo (h / 2) h) :=
      hφ'.mono (by grind)
    refine hd.congr ?_
    intro y hy
    refine Real.ext_cauchy (congrArg Real.cauchy (eq2 (by grind) m ?_))
    exact (hφ.contDiffWithinAt (by grind)).contDiffAt
        (by simp only [Set.mem_Ioo, Icc_mem_nhds_iff] at hy ⊢; exact ⟨by linarith, by linarith⟩)
  have hf2' : DifferentiableOn ℝ (iteratedDerivWithin 2 (fun x ↦ F (h - x)) (Set.Icc (h / 2) h))
      (Set.Ioo (h / 2) h) := by
    refine hf1' 2 ?_ ?_
    · exact ContDiffOn.congr t2' fun x ↦ congrFun rfl
    · have : (iteratedDerivWithin 2 (fun x ↦ F (h - x)) (Set.Icc 0 h))
        = fun x ↦ (iteratedDerivWithin 2 F (Set.Icc 0 h)) (h - x) := by

        sorry
      simp [this]

      -- #check DifferentiableOn.sub (differentiable_const h) differentiable_id
      -- #check (differentiable_const.sub differentiable_id).contDiffOn
      sorry
  obtain ⟨ξ1, hξ1, hξ1_rem⟩ := useful h1 (F := F) t1 (hf1' 2 hf hf')
  obtain ⟨ζ, hζ, hζ_rem⟩ := useful h1 (F := fun x => F (h - x)) t2 hf2'
  have eq1 : derivWithin F (Set.Icc (h / 2) h) (h / 2) = derivWithin F (Set.Icc 0 h) (h / 2) := by

    sorry
  have eq2 : iteratedDerivWithin 2 F (Set.Icc (h / 2) h) (h / 2)
      = iteratedDerivWithin 2 F (Set.Icc 0 h) (h / 2) := by
    refine eq2 (y := h/2) (by grind) ?_ ?_

    
    sorry
  have eq3 : derivWithin (fun x ↦ F (h - x)) (Set.Icc (h / 2) h) (h / 2)
    = derivWithin (fun x ↦ F (h - x)) (Set.Icc 0 h) (h / 2) := by
    sorry
  have eq4 : iteratedDerivWithin 2 (fun x ↦ F (h - x)) (Set.Icc (h / 2) h) (h / 2)
      = iteratedDerivWithin 2 (fun x ↦ F (h - x)) (Set.Icc 0 h) (h / 2) := by

    sorry
  have eq5 : iteratedDerivWithin 3 (fun x ↦ F (h - x)) (Set.Icc (h / 2) h) ζ
    = iteratedDerivWithin 3 (fun x ↦ F (h - x)) (Set.Icc 0 h) ζ := by
    sorry
  norm_num [-one_div, sub_half, eq1, eq2, eq3, eq4] at hξ1 hζ hξ1_rem hζ_rem
  calc
  _ = |F h - (F (h/2) + h / 2 * derivWithin F (Icc 0 h) (h/2)
    + 1 / 2 * (h/2) ^ 2 * iteratedDerivWithin 2 F (Icc 0 h) (h/2))
      - (F 0 - (F (h/2) + h/2 * derivWithin (fun x ↦ F (h - x)) (Icc 0 h) (h/2) +
      1 / 2 * (h/2) ^ 2 * iteratedDerivWithin 2 (fun x ↦ F (h - x)) (Icc 0 h) (h/2)))| := by
    rw [iteratedDerivWithin_comp_const_sub (hx := by grind) (uniqueDiffOn_Icc hh) hf]
    simpa [derivWithin_comp_const_sub, sub_half, field] using by ring_nf
  _ = |h ^ 3 / 48 * iteratedDerivWithin 3 F (Icc 0 h) ξ1
    + h ^ 3 / 48 * iteratedDerivWithin 3 F (Icc 0 h) (h - ζ)| := by
    -- rw [hξ1_rem, hζ_rem]
    -- congr 1
    -- simp [eq5, field, mul_assoc, iteratedDerivWithin_comp_const_sub]
    sorry

  _ ≤ _ := by sorry
  /-



  -/

-- theorem midpoint_rule_error {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
--     (h_df : DifferentiableOn ℝ f (Icc a b))
--     (h_ddf : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b))
--     (h_ddf_integrable : IntervalIntegrable (iteratedDerivWithin 2 f (Icc a b)) volume a b) :
--     ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - f ((a + b) / 2) * (b - a)
--       = (b - a)^3 / 24 * (iteratedDeriv 2 f ξ) := by
--   set h : ℝ := b - a with hdef
--   set g : ℝ → ℝ := fun x => f (x + a) with gdef
--   let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
--   have : ContinuousOn f (Set.Icc a b) := by
--     fun_prop
--   have hg : ContinuousOn g (Icc 0 h) := by
--     simp [gdef]
--     sorry
--   have hFderiv : deriv F = g := by
--     funext x
--     sorry-- simpa [F] using hg.deriv_integral g 0 x
--   have hFcont : ContDiffOn ℝ 3 F (Icc 0 h) := sorry
--   rcases midpoint_aux (F := F) (sub_pos.mpr hab) hFcont with ⟨ξ0, hξ0, hEq⟩
--   refine ⟨a + ξ0, by grind, ?_⟩
--   have hDerivMid : deriv F (h / 2) = f ((a + b) / 2) := by
--     simp [hFderiv, g, add_comm, hdef]
--     ring_nf
--   have hIter3 : iteratedDeriv 3 F ξ0 = iteratedDeriv 2 f (a + ξ0) := by calc
--     _ = iteratedDeriv 2 (deriv F) ξ0 := congrArg (fun u ↦ u ξ0) iteratedDeriv_succ'
--     _ = _ := by rw [hFderiv, gdef, iteratedDeriv_comp_add_const, add_comm]
--   have hEq' : F h - deriv F (h / 2) * h = (h^3 / 24) * iteratedDeriv 3 F ξ0 := by
--     simpa [F] using hEq
--   have hFh : F h = (∫ x in a..b, f x) := by simp [F, g, h, add_comm]
--   simpa only [hFh, hDerivMid, hIter3] using hEq'
