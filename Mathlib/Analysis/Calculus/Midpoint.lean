/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Tactic.Field

/-!
# Simpson's Midpoint Rule

This file contains a definition of integration via Simpson's midpoint rule, along with
an error bound in terms of a bound on the third derivative of the antiderivative.

## Main results
- `midpoint_error_le`: the convergence theorem for Simpson's midpoint rule.
- `midpoint_composite_error_le`: the composite midpoint rule error bound.

## References
We follow the standard proof for the error bound of the midpoint rule.
-/

public section

open MeasureTheory intervalIntegral Interval Finset HasDerivWithinAt Set

/-- Integration of `f` from `a` to `b` using Simpson's midpoint rule with `N` subintervals.
This uses the midpoint of each subinterval: `∫_a^b f(x) dx ≈ h * ∑_{i=0}^{n-1} f(x_{i+1/2})`
where `h = (b - a) / n` and `x_{i+1/2} = a + (i + 1/2) * h`. -/
noncomputable def midpoint_integral (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ((b - a) / N) * ∑ k ∈ range N, f (a + (k + 1 / 2 : ℝ) * (b - a) / N)

/-- The absolute error of Simpson's midpoint integration. -/
noncomputable def midpoint_error (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  (midpoint_integral f N a b) - (∫ x in a..b, f x)

/-- Just like exact integration, the Simpson midpoint approximation retains the same magnitude but
changes sign when the endpoints are swapped. -/
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

/-- The absolute error of Simpson's midpoint rule does not change when the endpoints are swapped. -/
theorem midpoint_error_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    midpoint_error f N a b = -midpoint_error f N b a := by
  unfold midpoint_error
  rw [midpoint_integral_symm f N_nonzero a b, intervalIntegral.integral_symm]
  ring

/-- Just like exact integration, the Simpson midpoint integration from `a` to `a` is zero. -/
@[simp]
theorem midpoint_integral_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) :
    midpoint_integral f N a a = 0 := by
  simp [midpoint_integral]

/-- The error of Simpson's midpoint integration from `a` to `a` is zero. -/
@[simp]
theorem midpoint_error_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) :
    midpoint_error f N a a = 0 := by
  simp [midpoint_error]

/-- An exact formula for integration with a single midpoint evaluation. -/
@[simp]
theorem midpoint_integral_one (f : ℝ → ℝ) (a b : ℝ) :
    midpoint_integral f 1 a b = (b - a) * f ((a + b) / 2) := by
  simp only [midpoint_integral, Nat.cast_one, range_one, sum_singleton]
  ring_nf

/-- A basic Simpson midpoint equivalent to `IntervalIntegral.sum_integral_adjacent_intervals`. More
general theorems can be derived from repeated applications of this one. -/
theorem sum_midpoint_integral_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ}
    (N_nonzero : 0 < N) : ∑ i ∈ range N, midpoint_integral f 1 (a + i * h) (a + (i + 1) * h)
      = midpoint_integral f N a (a + N * h) := by
  simp_rw [midpoint_integral_one, add_sub_add_left_eq_sub, ← sub_mul, midpoint_integral,
    add_sub_cancel_left, one_mul, ← mul_sum, ← mul_div, show N * (h / N) = h by field]
  congr; ext; congr; field

/-- A simplified version of the previous theorem, for use in proofs by induction and the like. -/
theorem midpoint_integral_ext {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : 0 < N) :
    midpoint_integral f N a (a + N * h) + midpoint_integral f 1 (a + N * h) (a + (N + 1) * h)
      = midpoint_integral f (N + 1) a (a + (N + 1) * h) := by
  rw [← Nat.cast_add_one, ← sum_midpoint_integral_adjacent_intervals N_nonzero,
      ← sum_midpoint_integral_adjacent_intervals (Nat.add_pos_left N_nonzero 1),
      sum_range_succ, Nat.cast_add_one]

/-- Since we have `sum_[]_adjacent_intervals` theorems for both exact and Simpson midpoint
integration, it's natural to combine them into a similar formula for the error. This theorem is in
particular used in the proof of the general error bound. -/
theorem sum_midpoint_error_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (hpos : 0 < h)
    (N_nonzero : 0 < N) (h_f_int : IntervalIntegrable f volume a (a + N * h)) :
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

private lemma midpoint_error_le_of_lt' {F : ℝ → ℝ} {M : ℝ} {a b : ℝ} (a_lt_b : a < b)
    (hF : ContDiffOn ℝ 2 F (Icc a b))
    (hF_diff : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc a b)) (Ioo a b))
    (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
    |F b - F a - (derivWithin F (Icc a b) ((a + b) / 2)) * (b - a)| ≤ (b - a) ^ 3 * M / 24 := by
  set m := (a + b) / 2 with hm_def
  have h_m_lt_b : m < b := by linarith [a_lt_b]
  set E := F b - F a - (derivWithin F (Icc a b) m) * (b - a) with hE_def
  have hF_diff_Ioo : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc a b)) (Ioo a b) := hF_diff
  have h_m_in_Icc : m ∈ Icc a b := by grind
  obtain ⟨ξ₁, hξ₁_in, hξ₁_eq⟩ : ∃ ξ₁ ∈ Ioo m b, F b = F m + (derivWithin F (Icc a b) m) * (b - m) +
            (iteratedDerivWithin 2 F (Icc a b) m) * (b - m) ^ 2 / 2 +
            (iteratedDerivWithin 3 F (Icc a b) ξ₁) * (b - m) ^ 3 / 6 := by
    have hF_mb : ContDiffOn ℝ 2 F (Icc m b) := hF.mono (by grind)
    have hF_cdAt_m : ContDiffAt ℝ 2 F m := hF.contDiffAt (by grind [Icc_mem_nhds_iff])
    have hF_diffAt_m : DifferentiableAt ℝ F m := hF_cdAt_m.differentiableAt (Ne.symm (NeZero.ne' 2))
    have h_set_eq_at : ∀ x ∈ Ioo m b, Icc m b =ᶠ[nhds x] Icc a b := by
      intro x hx
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact propext ⟨fun _ => ⟨by grind, hy.2.le⟩,
                     fun _ => ⟨hy.1.le, hy.2.le⟩⟩
    have h_iDW2_eq : ∀ x ∈ Ioo m b,
        iteratedDerivWithin 2 F (Icc m b) x = iteratedDerivWithin 2 F (Icc a b) x := by
      intro x hx
      simp only [iteratedDerivWithin]
      congr 1
      exact iteratedFDerivWithin_congr_set (h_set_eq_at x hx) 2
    have hF_diff_mb : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc m b)) (Ioo m b) := by
      intro x hx
      have h_diff_ab : DifferentiableWithinAt ℝ (iteratedDerivWithin 2 F (Icc a b)) (Ioo m b) x :=
        (hF_diff_Ioo x ⟨by grind, hx.2⟩).mono (by grind)
      exact h_diff_ab.congr (fun y hy => h_iDW2_eq y hy) (h_iDW2_eq x hx)
    obtain ⟨ξ₁, hξ₁_in, hξ₁_eq⟩ := taylor_mean_remainder_lagrange h_m_lt_b hF_mb hF_diff_mb
    refine ⟨ξ₁, hξ₁_in, ?_⟩
    have h_deriv_m_eq : derivWithin F (Icc m b) m = derivWithin F (Icc a b) m := by
      rw [hF_diffAt_m.derivWithin (uniqueDiffOn_Icc h_m_lt_b m (left_mem_Icc.mpr h_m_lt_b.le)),
        hF_diffAt_m.derivWithin (uniqueDiffOn_Icc a_lt_b m h_m_in_Icc)]
    have h_iDW2_m_eq : iteratedDerivWithin 2 F (Icc m b) m
                     = iteratedDerivWithin 2 F (Icc a b) m := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h_m_lt_b) hF_cdAt_m
        (left_mem_Icc.mpr h_m_lt_b.le), iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc a_lt_b) hF_cdAt_m h_m_in_Icc]
    have h_iDW3_eq : iteratedDerivWithin 3 F (Icc m b) ξ₁
        = iteratedDerivWithin 3 F (Icc a b) ξ₁ := by
      simp only [iteratedDerivWithin]
      congr 1
      exact iteratedFDerivWithin_congr_set (h_set_eq_at ξ₁ hξ₁_in) 3
    have h_taylEval : taylorWithinEval F 2 (Icc m b) m b =
        F m + (b - m) * derivWithin F (Icc m b) m +
        (b - m) ^ 2 / 2 * iteratedDerivWithin 2 F (Icc m b) m := by
      rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
          iteratedDerivWithin_one]
      simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one]
      ring
    rw [h_taylEval, h_deriv_m_eq, h_iDW2_m_eq, h_iDW3_eq] at hξ₁_eq
    rw [eq_add_of_sub_eq' hξ₁_eq]
    congr 1
    ring
  obtain ⟨ξ₂, hξ₂_in, hξ₂_eq⟩ : ∃ ξ₂ ∈ Ioo a m,
      F a = F m + (derivWithin F (Icc a b) m) * (a - m) +
            (iteratedDerivWithin 2 F (Icc a b) m) * (a - m) ^ 2 / 2 +
            (iteratedDerivWithin 3 F (Icc a b) ξ₂) * (a - m) ^ 3 / 6 := by
    set c := a + b with hc_def
    have hcm : c - m = m := by linarith [hm_def, hc_def]
    have hGb : F (c - b) = F a := by grind
    have hGm : F (c - m) = F m := by rw [hcm]
    have hφ_maps : Set.MapsTo (fun t => c - t) (Icc m b) (Icc a b) := fun t ht ↦ by grind
    have hG_mb : ContDiffOn ℝ 2 (fun t => F (c - t)) (Icc m b) :=
      hF.comp (contDiffOn_const.sub contDiffOn_id) hφ_maps
    have hF_cdAt_m : ContDiffAt ℝ 2 F m := hF.contDiffAt (by grind [Icc_mem_nhds])
    have hF_diffAt_m : DifferentiableAt ℝ F m := hF_cdAt_m.differentiableAt (Ne.symm (NeZero.ne' 2))
    have hG_cdAt_m : ContDiffAt ℝ 2 (fun t => F (c - t)) m := by
      apply ContDiffAt.comp m _ (contDiffAt_const.sub contDiffAt_id)
      simpa only [id, hcm]
    have hG_diffAt_m : DifferentiableAt ℝ (fun t => F (c - t)) m :=
      hG_cdAt_m.differentiableAt (Ne.symm (NeZero.ne' 2))
    have hG_cdAt_of_mem : ∀ x ∈ Ioo m b, ContDiffAt ℝ 2 (fun t => F (c - t)) x := by
      intro x hx
      apply ContDiffAt.comp x _ (contDiffAt_const.sub contDiffAt_id)
      apply hF.contDiffAt
      grind [Icc_mem_nhds]
    have h_iDW2_G_eq : ∀ x ∈ Ioo m b, iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b) x
          = iteratedDerivWithin 2 F (Icc a b) (c - x) := by
      intro x hx
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h_m_lt_b) (hG_cdAt_of_mem x hx)
        ⟨hx.1.le, hx.2.le⟩, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc a_lt_b)
        (hF.contDiffAt (by grind[Icc_mem_nhds])) (by grind)]
      have h := iteratedDeriv_comp_const_sub 2 F c
      simp only [neg_one_sq, one_smul] at h
      exact congr_fun h x
    have hG_diff_mb : DifferentiableOn ℝ (iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b))
        (Ioo m b) := by
      intro x hx
      have hcx_ab : c - x ∈ Ioo a b := by grind
      apply DifferentiableWithinAt.congr
      · exact DifferentiableWithinAt.comp x (hF_diff_Ioo (c - x) hcx_ab)
          ((differentiableAt_const c).sub differentiableAt_id).differentiableWithinAt
          (fun t th ↦ by grind)
      · intro y hy; exact h_iDW2_G_eq y hy
      · exact h_iDW2_G_eq x hx
    obtain ⟨ξ, hξ_in, hξ_eq⟩ := taylor_mean_remainder_lagrange h_m_lt_b hG_mb hG_diff_mb
    refine ⟨c - ξ, by grind, ?_⟩
    have h_taylEval_G : taylorWithinEval (fun t => F (c - t)) 2 (Icc m b) m b =
        F (c - m) + (b - m) * derivWithin (fun t => F (c - t)) (Icc m b) m +
        (b - m) ^ 2 / 2 * iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b) m := by
      rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
          iteratedDerivWithin_one]
      simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one]
      ring
    have h_deriv_G_m : derivWithin (fun t => F (c - t)) (Icc m b) m
        = -(derivWithin F (Icc a b) m) := by
      rw [hG_diffAt_m.derivWithin (uniqueDiffOn_Icc h_m_lt_b m (left_mem_Icc.mpr h_m_lt_b.le)),
        hF_diffAt_m.derivWithin (uniqueDiffOn_Icc a_lt_b m h_m_in_Icc)]
      have hg : HasDerivAt F (deriv F m) (c - m) := by
        rw [hcm]; exact hF_diffAt_m.hasDerivAt
      have h1 : HasDerivAt (fun t => F (c - t)) (deriv F m * (-1)) m :=
        hg.comp m ((hasDerivAt_id m).const_sub c)
      linarith [h1.deriv]
    have h_iDW2_G_m : iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b) m
        = iteratedDerivWithin 2 F (Icc a b) m := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h_m_lt_b) hG_cdAt_m
        (left_mem_Icc.mpr h_m_lt_b.le), iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc a_lt_b) hF_cdAt_m h_m_in_Icc]
      have h := iteratedDeriv_comp_const_sub 2 F c
      simp only [neg_one_sq, one_smul] at h
      have := congr_fun h m
      simpa only [hcm] using this
    have : iteratedDerivWithin 3 (fun t => F (c - t)) (Icc m b) ξ
        = -(iteratedDerivWithin 3 F (Icc a b) (c - ξ)) := by
      have hcξ_ab : c - ξ ∈ Ioo a b := by grind
      rw [iteratedDerivWithin_succ]
      have h_hdw_phi : HasDerivWithinAt (fun t => c - t) (-1) (Icc m b) ξ :=
        ((hasDerivAt_id ξ).const_sub c).hasDerivWithinAt
      have h_hdw_g : HasDerivWithinAt (iteratedDerivWithin 2 F (Icc a b))
          (iteratedDerivWithin 3 F (Icc a b) (c - ξ)) (Icc a b) (c - ξ) := by
        rw [iteratedDerivWithin_succ]
        exact ((hF_diff_Ioo (c - ξ) hcξ_ab).differentiableAt
          (Ioo_mem_nhds hcξ_ab.1 hcξ_ab.2)).differentiableWithinAt.hasDerivWithinAt
      have h_hdw_comp : HasDerivWithinAt (fun t => iteratedDerivWithin 2 F (Icc a b) (c - t))
          (iteratedDerivWithin 3 F (Icc a b) (c - ξ) * (-1)) (Icc m b) ξ :=
        h_hdw_g.comp ξ h_hdw_phi hφ_maps
      have h_ev_eq : (fun t => iteratedDerivWithin 2 (fun s => F (c - s)) (Icc m b) t)
          =ᶠ[nhdsWithin ξ (Icc m b)] (fun t => iteratedDerivWithin 2 F (Icc a b) (c - t)) := by
        apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
        filter_upwards [IsOpen.mem_nhds isOpen_Ioo hξ_in] with y hy
        exact h_iDW2_G_eq y hy
      have h_hdw_iDW2 : HasDerivWithinAt (iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b))
          (iteratedDerivWithin 3 F (Icc a b) (c - ξ) * (-1)) (Icc m b) ξ :=
        h_hdw_comp.congr_of_eventuallyEq h_ev_eq (h_iDW2_G_eq ξ hξ_in)
      rw [h_hdw_iDW2.derivWithin (uniqueDiffOn_Icc h_m_lt_b ξ ⟨hξ_in.1.le, hξ_in.2.le⟩)]
      ring
    norm_num [Nat.factorial] at hξ_eq
    grind
  have h_pos : 0 < b - a := by linarith [a_lt_b]
  have h_final_bound : |E| ≤ (b - a) ^ 3 * M / 24 := by calc
    _ = |((iteratedDerivWithin 3 F (Icc a b) ξ₁) + (iteratedDerivWithin 3 F (Icc a b) ξ₂)) *
        (b - a) ^ 3 / 48| := by
      congr
      rw [hE_def, hξ₁_eq, hξ₂_eq]
      ring
    _ ≤ (|(iteratedDerivWithin 3 F (Icc a b) ξ₁)| + |(iteratedDerivWithin 3 F (Icc a b) ξ₂)|) *
        (b - a) ^ 3 / 48 := by
      have h_ba3_nn : (0 : ℝ) ≤ (b - a) ^ 3 := by positivity
      rw [abs_div, abs_mul, abs_of_nonneg h_ba3_nn, abs_of_pos (by norm_num : (0:ℝ) < 48)]
      gcongr
      exact abs_add_le _ _
    _ ≤ (M + M) * (b - a) ^ 3 / 48 := by
      have := fpp_bound ξ₁
      have := fpp_bound ξ₂
      gcongr
    _ = (b - a) ^ 3 * M / 24 := by ring
  rwa [hE_def] at h_final_bound

/-- The standard error bound for Simpson's midpoint integration on a single interval `[[a, b]]`.

For a function `F` with `F' = f`, if `F` is twice continuously differentiable on `[[a, b]]`,
the second derivative is differentiable on `(a, b)`, and the third derivative is bounded by `M`,
then the midpoint rule error is bounded by `|b - a|^3 * M / 24`. -/
theorem midpoint_error_le {F : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiffOn ℝ 2 F (uIcc a b))
    (hF_diff : DifferentiableOn ℝ (iteratedDerivWithin 2 F (uIcc a b)) (uIoo a b))
    {M : ℝ} (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (uIcc a b) x| ≤ M) :
    |F b - F a - (derivWithin F (uIcc a b) ((a + b) / 2)) * (b - a)| ≤ |b - a| ^ 3 * M / 24 := by
  rcases lt_trichotomy a b with h_lt | h_eq | h_gt
  · rw [uIcc_of_lt h_lt, uIoo_of_lt h_lt] at *
    rw [abs_of_pos (sub_pos.mpr h_lt)]
    exact midpoint_error_le_of_lt' h_lt hF hF_diff fpp_bound
  · simp [h_eq]
  · rw [uIcc_of_gt h_gt, uIoo_of_gt h_gt] at *
    rw [abs_of_neg (sub_neg.mpr h_gt), neg_sub]
    calc
      _ = |F a - F b - _root_.derivWithin F (Set.Icc b a) ((b + a) / 2) * (a - b)| := by grind
      _ ≤ _ := midpoint_error_le_of_lt' h_gt hF hF_diff fpp_bound

-- /-- The error bound for Simpson's midpoint integration in the case where `F` is `C^3`.

-- If `F` is three times continuously differentiable on `[[a, b]]` and the third derivative
-- is bounded by `M`, then the midpoint rule error is bounded by `|b - a|^3 * M / 24`. -/
-- theorem midpoint_error_le_of_c3 {F : ℝ → ℝ} {a b : ℝ}
--     (hF_c3 : ContDiffOn ℝ 3 F (Icc a b)) {M : ℝ}
--     (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
--     |F b - F a - (derivWithin F (Icc a b) ((a + b) / 2)) * (b - a)| ≤ |b - a| ^ 3 * M / 24 := by
--   sorry

-- /-- The composite Simpson's midpoint rule error bound.

-- For `F` with `F' = f`, the error in approximating `∫_a^b f(x) dx` by the midpoint sum
-- `h * ∑_{i=0}^{n-1} f(x_{i+1/2})` is bounded by `(h^2 / 24) * M * |b - a|`
-- where `h = (b-a)/n` and `M` bounds `|F'''|`.

-- Equivalently, since `|b - a| = n * h`, the bound can be written as `(h^2 / 24) * M * (b - a)`. -/
-- theorem midpoint_composite_error_le {F : ℝ → ℝ} {a b : ℝ} {N : ℕ} (N_nonzero : 0 < N)
--     (hF_c3 : ContDiffOn ℝ 3 F (Icc a b)) {M : ℝ}
--     (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
--     let h := (b - a) / N
--     |midpoint_error F N a b| ≤ (h ^ 2 / 24) * M * |b - a| := by
--   sorry

end
