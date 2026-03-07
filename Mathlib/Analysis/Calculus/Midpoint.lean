/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Field

/-!
# Simpson's Midpoint Rule

This file contains a definition of integration via Simpson's midpoint rule, along with
an error bound in terms of a bound on the third derivative of the antiderivative.

## Main results
- `simpson_midpoint_error_le`: the convergence theorem for Simpson's midpoint rule.
- `simpson_midpoint_composite_error_le`: the composite midpoint rule error bound.

## References
We follow the standard proof for the error bound of the midpoint rule.
-/

@[expose] public section

open MeasureTheory intervalIntegral Interval Finset HasDerivWithinAt Set

/-- Integration of `f` from `a` to `b` using Simpson's midpoint rule with `N` subintervals.
This uses the midpoint of each subinterval: `∫_a^b f(x) dx ≈ h * ∑_{i=0}^{n-1} f(x_{i+1/2})`
where `h = (b - a) / n` and `x_{i+1/2} = a + (i + 1/2) * h`. -/
noncomputable def simpson_midpoint_integral (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ((b - a) / N) * ∑ k ∈ range N, f (a + (k + 1 / 2 : ℝ) * (b - a) / N)

/-- The absolute error of Simpson's midpoint integration. -/
noncomputable def simpson_midpoint_error (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  (simpson_midpoint_integral f N a b) - (∫ x in a..b, f x)

/-- Just like exact integration, the Simpson midpoint approximation retains the same magnitude but
changes sign when the endpoints are swapped. -/
theorem simpson_midpoint_integral_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    simpson_midpoint_integral f N a b = -(simpson_midpoint_integral f N b a) := by
  unfold simpson_midpoint_integral
  have h_coeff : (b - a) / N = -((a - b) / N) := by ring
  have h_sum : ∑ k ∈ range N, f (a + (k + (1 / 2 : ℝ)) * (b - a) / N)
             = ∑ k ∈ range N, f (b + (k + (1 / 2 : ℝ)) * (a - b) / N) := by
    rw [← Finset.sum_range_reflect (fun k => f (b + (k + (1 / 2 : ℝ)) * (a - b) / N)) N]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    have h_eq : a + (k + (1 / 2 : ℝ)) * (b - a) / N
              = b + ((N - 1 - k : ℕ) + (1 / 2 : ℝ)) * (a - b) / N := by
      calc
        _ = a + (k + (1 / 2 : ℝ)) * (b - a) / N := rfl
        _ = b + ((N : ℝ) - 1 - k + (1 / 2 : ℝ)) * (a - b) / N := by field
        _ = b + (((N - 1 - k : ℕ) : ℝ) + (1 / 2 : ℝ)) * (a - b) / N := by
          have h6 : (k : ℕ) ≤ N - 1 := by omega
          have h7 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
            rw [Nat.cast_sub (by linarith : 1 ≤ N)]
            simp
          have h8 : ((N - 1 - k : ℕ) : ℝ) = ((N - 1 : ℕ) : ℝ) - k := by
            rw [Nat.cast_sub h6]
          rw [h8, h7]
        _ = b + ((N - 1 - k : ℕ) + (1 / 2 : ℝ)) * (a - b) / N := by
          norm_cast
    rw [h_eq]
  rw [h_coeff, h_sum]
  ring

/-- The absolute error of Simpson's midpoint rule does not change when the endpoints are swapped. -/
theorem simpson_midpoint_error_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    simpson_midpoint_error f N a b = -simpson_midpoint_error f N b a := by
  unfold simpson_midpoint_error
  rw [simpson_midpoint_integral_symm f N_nonzero a b, intervalIntegral.integral_symm]
  ring

/-- Just like exact integration, the Simpson midpoint integration from `a` to `a` is zero. -/
@[simp]
theorem simpson_midpoint_integral_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) :
    simpson_midpoint_integral f N a a = 0 := by
  simp [simpson_midpoint_integral]

/-- The error of Simpson's midpoint integration from `a` to `a` is zero. -/
@[simp]
theorem simpson_midpoint_error_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) :
    simpson_midpoint_error f N a a = 0 := by
  unfold simpson_midpoint_error
  simp

/-- An exact formula for integration with a single midpoint evaluation. -/
@[simp]
theorem simpson_midpoint_integral_one (f : ℝ → ℝ) (a b : ℝ) :
    simpson_midpoint_integral f 1 a b = (b - a) * f ((a + b) / 2) := by
  unfold simpson_midpoint_integral
  simp only [Nat.cast_one, range_one, sum_singleton]
  ring_nf

/-- A basic Simpson midpoint equivalent to `IntervalIntegral.sum_integral_adjacent_intervals`. More
general theorems can be derived from repeated applications of this one. -/
theorem sum_simpson_midpoint_integral_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ}
    (N_nonzero : 0 < N) :
    ∑ i ∈ range N, simpson_midpoint_integral f 1 (a + i * h) (a + (i + 1) * h)
      = simpson_midpoint_integral f N a (a + N * h) := by
  have h1 : ∀ i ∈ range N, simpson_midpoint_integral f 1 (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h)
              = h * f (a + ((i : ℝ) + 1 / 2) * h) := by
    intro i hi
    rw [simpson_midpoint_integral_one]
    congr
    · ring
    · field
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have h3 : (a + N * h - a) / N = h := by
    field_simp [Nat.cast_ne_zero.mpr N_nonzero.ne']
    ring_nf
  rw [simpson_midpoint_integral]
  congr 1
  · rw [h3]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  field_simp [Nat.cast_ne_zero.mpr N_nonzero.ne']
  ring

/-- A simplified version of the previous theorem, for use in proofs by induction and the like. -/
theorem simpson_midpoint_integral_ext {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : 0 < N) :
    simpson_midpoint_integral f N a (a + N * h) + simpson_midpoint_integral f 1 (a + N * h)
    (a + (N + 1) * h) = simpson_midpoint_integral f (N + 1) a (a + (N + 1) * h) := by
  have h1 : simpson_midpoint_integral f 1 (a + N * h) (a + (N + 1) * h)
          = h * f (a + (N + 1 / 2 : ℝ) * h) := by
    rw [simpson_midpoint_integral_one]
    congr
    · ring
    · field
  have h2 : (a + N * h - a) / N = h := by
    field_simp [Nat.cast_ne_zero.mpr N_nonzero.ne']
    ring_nf
  have h3 : (a + (N + 1 : ℝ) * h - a) / (N + 1) = h := by
    field_simp [Nat.cast_ne_zero.mpr N_nonzero.ne']
    ring_nf
  rw [simpson_midpoint_integral, h2, h1]
  have h4 : ∀ k ∈ Finset.range N, f (a + (k + (1 / 2 : ℝ)) * (a + N * h - a) / N)
                              = f (a + (k + (1 / 2 : ℝ)) * h) := by
    intro k hk
    congr 1
    field_simp [Nat.cast_ne_zero.mpr N_nonzero.ne']
    ring
  have h5 : ∑ k ∈ Finset.range N, f (a + (k + (1 / 2 : ℝ)) * (a + N * h - a) / N)
          = ∑ k ∈ Finset.range N, f (a + (k + (1 / 2 : ℝ)) * h) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [h4 k hk]
  rw [h5]
  simp only [simpson_midpoint_integral]
  have h6 : ∑ k ∈ range (N + 1), f (a + (k + (1 / 2 : ℝ)) * h)
          = ∑ k ∈ range (N + 1), f (a + (k + (1 / 2 : ℝ)) * (a + (N + 1) * h - a) / (N + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    field_simp [Nat.cast_ne_zero.mpr N_nonzero.ne']
    ring
  have h7 : (↑N + 1 : ℝ) = ↑(N + 1) := by norm_cast
  calc
    h * ∑ k ∈ range N, f (a + (k + (1 / 2 : ℝ)) * h) + h * f (a + (N + 1 / 2 : ℝ) * h)
      = h * (∑ k ∈ range N, f (a + (k + (1 / 2 : ℝ)) * h) + f (a + (N + 1 / 2 : ℝ) * h)) := by
      rw [mul_add]
    _ = h * ∑ k ∈ range (N + 1), f (a + (k + (1 / 2 : ℝ)) * h) := by rw [Finset.sum_range_succ]
    _ = h * ∑ k ∈ range (N + 1), f (a + (k + (1 / 2 : ℝ)) * (a + (N + 1) * h - a) / (N + 1)) := by
      rw [h6]
    _ = (a + (N + 1 : ℝ) * h - a) / (↑N + 1) * ∑ k ∈ range (N + 1), f (a + (k + (1 / 2 : ℝ)) *
      (a + (N + 1) * h - a) / (↑N + 1)) := by
      rw [h3]
    _ = (a + (N + 1 : ℝ) * h - a) / ↑(N + 1) * ∑ k ∈ range (N + 1), f (a + (k + (1 / 2 : ℝ)) *
      (a + (N + 1) * h - a) / ↑(N + 1)) := by
      rw [h7]

/-- Since we have `sum_[]_adjacent_intervals` theorems for both exact and Simpson midpoint
integration, it's natural to combine them into a similar formula for the error. This theorem is in
particular used in the proof of the general error bound. -/
theorem sum_simpson_midpoint_error_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ}
    (N_nonzero : 0 < N) (h_f_int : IntervalIntegrable f volume a (a + N * h)) :
    ∑ i ∈ range N, simpson_midpoint_error f 1 (a + i * h) (a + (i + 1) * h)
      = simpson_midpoint_error f N a (a + N * h) := by
  simp only [simpson_midpoint_error]
  have h1 : ∑ i ∈ range N, (simpson_midpoint_integral f 1 (a + i * h) (a + (i + 1) * h) -
      ∫ x in a + i * h..a + (i + 1) * h, f x)
      = ∑ i ∈ range N, simpson_midpoint_integral f 1 (a + i * h) (a + (i + 1) * h) -
      ∑ i ∈ range N, ∫ x in a + i * h..a + (i + 1) * h, f x := by
    rw [Finset.sum_sub_distrib]
  rw [h1, sum_simpson_midpoint_integral_adjacent_intervals N_nonzero]
  have h3 : ∑ i ∈ range N, ∫ x in a + i * h..a + (i + 1) * h, f x = ∫ x in a..a + N * h, f x := by
    let a' : ℕ → ℝ := fun k => a + k * h
    have h_int : ∀ k < N, IntervalIntegrable f volume (a' k) (a' (k + 1)) := by
      intro k hk
      apply h_f_int.mono_set
      apply Set.uIcc_subset_uIcc
      · simp only [Set.mem_uIcc, a']
        rcases lt_trichotomy 0 h with hh | hh | hh
        · left
          constructor
          · nlinarith
          · have : (k : ℝ) ≤ N := Nat.cast_le.2 hk.le
            nlinarith
        · left
          constructor <;> nlinarith
        · right
          constructor
          · have : (k : ℝ) ≤ N := Nat.cast_le.2 hk.le
            nlinarith
          · nlinarith
      · simp only [Set.mem_uIcc, a']
        rcases lt_trichotomy 0 h with hh | hh | hh
        · left
          constructor
          · nlinarith
          · have : (k + 1 : ℝ) ≤ N := by
              norm_cast
            have : (1 + ↑k) * h ≤ ↑N * h := by
              convert mul_le_mul_of_nonneg_right this hh.le using 1
              ring_nf
            grind
        · left
          constructor <;> nlinarith
        · right
          constructor
          · have : (k + 1 : ℝ) ≤ N := by
              norm_cast
            have : ↑N * h ≤ (1 + ↑k) * h := by
              convert mul_le_mul_of_nonpos_left this hh.le using 1
              <;> ring_nf
            have : a + ↑N * h ≤ a + (1 + ↑k) * h := by linarith
            have h_eq : a + ↑(k + 1) * h = a + (1 + ↑k) * h := by
              norm_cast
              ring_nf
            rw [h_eq]
            exact this
          · nlinarith
    have h_sum : ∑ k ∈ range N, ∫ x in a' k..a' (k + 1), f x = ∫ x in a' 0..a' N, f x :=
      sum_integral_adjacent_intervals h_int
    convert h_sum using 1
    · apply Finset.sum_congr rfl
      intro k _
      simp [a']
    · simp [a']
  rw [h3]

/-- The most basic case: error bound for the midpoint rule on a single interval with ordered
endpoints. Given `F` with `F' = f`, we bound `|(b-a) * F'((a+b)/2) - (F(b) - F(a))|`.

This is the key lemma: for `F` satisfying
`(hf : ContDiffOn ℝ 2 F (Icc 0 h))`
`(hf' : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc 0 h)) (Ioo 0 h))`
and `(fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc 0 h) x| ≤ M)`,
we have `|F h - F 0 - (derivWithin F (Icc 0 h) (h/2)) * h| ≤ (h^3 / 24) * M`. -/
private lemma simpson_midpoint_error_le_of_lt' {F : ℝ → ℝ} {M : ℝ} {a b : ℝ} (a_lt_b : a < b)
    (hF : ContDiffOn ℝ 2 F (Icc a b))
    (hF_diff : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc a b)) (Ioo a b))
    (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
    |F b - F a - (derivWithin F (Icc a b) ((a + b) / 2)) * (b - a)| ≤ (b - a) ^ 3 * M / 24 := by
  set m := (a + b) / 2 with hm_def
  set h := b - a with hh_def
  have h_m_in_Ioo : m ∈ Ioo a b := by
    constructor <;> linarith [a_lt_b]
  have h_a_lt_m : a < m := by
    linarith [a_lt_b]
  have h_m_lt_b : m < b := by
    linarith [a_lt_b]
  set E := F b - F a - (derivWithin F (Icc a b) m) * (b - a) with hE_def
  have hF_Icc : ContDiffOn ℝ 2 F (Icc a b) := hF
  have hF_diff_Ioo : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc a b)) (Ioo a b) := hF_diff
  have h_m_in_Icc : m ∈ Icc a b := by
    constructor <;> linarith [a_lt_b]
  have h_b_in_Icc : b ∈ Icc a b := by
    constructor <;> linarith [a_lt_b]
  have h_a_in_Icc : a ∈ Icc a b := by
    constructor <;> linarith [a_lt_b]
  have h_taylor_b : ∃ ξ₁ ∈ Ioo m b,
      F b = F m + (derivWithin F (Icc a b) m) * (b - m) +
            (iteratedDerivWithin 2 F (Icc a b) m) * (b - m) ^ 2 / 2 +
            (iteratedDerivWithin 3 F (Icc a b) ξ₁) * (b - m) ^ 3 / 6 := by
    have hF_mb : ContDiffOn ℝ 2 F (Icc m b) :=
      hF.mono (Icc_subset_Icc_left (le_of_lt h_a_lt_m))
    have hF_cdAt_m : ContDiffAt ℝ 2 F m :=
      hF.contDiffAt (Icc_mem_nhds h_a_lt_m h_m_lt_b)
    have hF_diffAt_m : DifferentiableAt ℝ F m :=
      hF_cdAt_m.differentiableAt (Ne.symm (NeZero.ne' 2))
    have h_set_eq_at : ∀ x ∈ Ioo m b, Icc m b =ᶠ[nhds x] Icc a b := by
      intro x hx
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact propext ⟨fun _ => ⟨(h_a_lt_m.trans hy.1).le, hy.2.le⟩,
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
        (hF_diff_Ioo x ⟨h_a_lt_m.trans hx.1, hx.2⟩).mono
          (Ioo_subset_Ioo_left h_a_lt_m.le)
      exact h_diff_ab.congr (fun y hy => h_iDW2_eq y hy) (h_iDW2_eq x hx)
    obtain ⟨ξ₁, hξ₁_in, hξ₁_eq⟩ := taylor_mean_remainder_lagrange h_m_lt_b hF_mb hF_diff_mb
    refine ⟨ξ₁, hξ₁_in, ?_⟩
    have h_deriv_m_eq : derivWithin F (Icc m b) m = derivWithin F (Icc a b) m := by
      rw [hF_diffAt_m.derivWithin (uniqueDiffOn_Icc h_m_lt_b m (left_mem_Icc.mpr h_m_lt_b.le))]
      rw [hF_diffAt_m.derivWithin (uniqueDiffOn_Icc a_lt_b m h_m_in_Icc)]
    have h_iDW2_m_eq : iteratedDerivWithin 2 F (Icc m b) m = iteratedDerivWithin 2 F (Icc a b) m :=
      by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h_m_lt_b) hF_cdAt_m
            (left_mem_Icc.mpr h_m_lt_b.le)]
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc a_lt_b) hF_cdAt_m h_m_in_Icc]
    have h_iDW3_eq : iteratedDerivWithin 3 F (Icc m b) ξ₁ = iteratedDerivWithin 3 F (Icc a b) ξ₁ :=
      by
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
    linarith
  have h_taylor_a : ∃ ξ₂ ∈ Ioo a m,
      F a = F m + (derivWithin F (Icc a b) m) * (a - m) +
            (iteratedDerivWithin 2 F (Icc a b) m) * (a - m) ^ 2 / 2 +
            (iteratedDerivWithin 3 F (Icc a b) ξ₂) * (a - m) ^ 3 / 6 := by
    set c := a + b with hc_def
    have hcm : c - m = m := by linarith [hm_def, hc_def]
    have hGb : F (c - b) = F a := by
      have : c - b = a := by linarith [hc_def]
      rw [this]
    have hGm : F (c - m) = F m := by rw [hcm]
    have hφ_maps : Set.MapsTo (fun t => c - t) (Icc m b) (Icc a b) := by
      intro t ht
      simp only [Set.mem_Icc] at ht ⊢
      constructor
      · linarith [ht.2]
      · linarith [ht.1, h_a_lt_m]
    have hG_mb : ContDiffOn ℝ 2 (fun t => F (c - t)) (Icc m b) :=
      hF.comp (contDiffOn_const.sub contDiffOn_id) hφ_maps
    have hF_cdAt_m : ContDiffAt ℝ 2 F m :=
      hF.contDiffAt (Icc_mem_nhds h_a_lt_m h_m_lt_b)
    have hF_diffAt_m : DifferentiableAt ℝ F m := hF_cdAt_m.differentiableAt (Ne.symm (NeZero.ne' 2))
    have hG_cdAt_m : ContDiffAt ℝ 2 (fun t => F (c - t)) m := by
      apply ContDiffAt.comp m _ (contDiffAt_const.sub contDiffAt_id)
      simp only [id, hcm]; exact hF_cdAt_m
    have hG_diffAt_m : DifferentiableAt ℝ (fun t => F (c - t)) m :=
      hG_cdAt_m.differentiableAt (Ne.symm (NeZero.ne' 2))
    have hG_cdAt_of_mem : ∀ x ∈ Ioo m b, ContDiffAt ℝ 2 (fun t => F (c - t)) x := by
      intro x hx
      apply ContDiffAt.comp x _ (contDiffAt_const.sub contDiffAt_id)
      apply hF.contDiffAt
      apply Icc_mem_nhds
      · simp only [id]; linarith [hx.2, hc_def]
      · simp only [id]; linarith [hx.1, h_a_lt_m, hc_def]
    have h_iDW2_G_eq : ∀ x ∈ Ioo m b,
        iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b) x
          = iteratedDerivWithin 2 F (Icc a b) (c - x) := by
      intro x hx
      have hcx_ab : c - x ∈ Ioo a b := by
        simp only [Set.mem_Ioo, hc_def]
        constructor <;> linarith [hx.1, hx.2, h_a_lt_m]
      have hF_cdAt_cx : ContDiffAt ℝ 2 F (c - x) :=
        hF.contDiffAt (Icc_mem_nhds hcx_ab.1 hcx_ab.2)
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h_m_lt_b)
            (hG_cdAt_of_mem x hx) ⟨hx.1.le, hx.2.le⟩]
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc a_lt_b)
            hF_cdAt_cx ⟨hcx_ab.1.le, hcx_ab.2.le⟩]
      have h := iteratedDeriv_comp_const_sub 2 F c
      simp only [neg_one_sq, one_smul] at h
      exact congr_fun h x
    have hG_diff_mb : DifferentiableOn ℝ (iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b))
        (Ioo m b) := by
      intro x hx
      have hcx_ab : c - x ∈ Ioo a b := by
        simp only [Set.mem_Ioo, hc_def]
        constructor <;> linarith [hx.1, hx.2, h_a_lt_m]
      apply DifferentiableWithinAt.congr
      · have h_comp : DifferentiableWithinAt ℝ
            (iteratedDerivWithin 2 F (Icc a b) ∘ (fun t => c - t)) (Ioo m b) x := by
          apply DifferentiableWithinAt.comp x (hF_diff_Ioo (c - x) hcx_ab)
          · exact ((differentiableAt_const c).sub differentiableAt_id).differentiableWithinAt
          · intro t ht
            simp only [Set.mem_Ioo] at ht ⊢
            constructor <;> linarith [ht.1, ht.2, h_a_lt_m]
        exact h_comp
      · intro y hy; exact h_iDW2_G_eq y hy
      · exact h_iDW2_G_eq x hx
    obtain ⟨ξ, hξ_in, hξ_eq⟩ := taylor_mean_remainder_lagrange h_m_lt_b hG_mb hG_diff_mb
    have hξ₂_in : c - ξ ∈ Ioo a m := by
      simp only [Set.mem_Ioo, hc_def]
      constructor <;> linarith [hξ_in.1, hξ_in.2]
    refine ⟨c - ξ, hξ₂_in, ?_⟩
    have h_taylEval_G : taylorWithinEval (fun t => F (c - t)) 2 (Icc m b) m b =
        F (c - m) + (b - m) * derivWithin (fun t => F (c - t)) (Icc m b) m +
        (b - m) ^ 2 / 2 * iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b) m := by
      rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
          iteratedDerivWithin_one]
      simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one]
      ring
    have h_deriv_G_m : derivWithin (fun t => F (c - t)) (Icc m b) m
        = -(derivWithin F (Icc a b) m) := by
      rw [hG_diffAt_m.derivWithin
            (uniqueDiffOn_Icc h_m_lt_b m (left_mem_Icc.mpr h_m_lt_b.le))]
      rw [hF_diffAt_m.derivWithin (uniqueDiffOn_Icc a_lt_b m h_m_in_Icc)]
      have h_neg : deriv (fun t => F (c - t)) m = -(deriv F m) := by
        have hg : HasDerivAt F (deriv F m) (c - m) := by
          rw [hcm]; exact hF_diffAt_m.hasDerivAt
        have h1 : HasDerivAt (fun t => F (c - t)) (deriv F m * (-1)) m :=
          hg.comp m ((hasDerivAt_id m).const_sub c)
        have h2 : deriv (fun t => F (c - t)) m = deriv F m * (-1) := h1.deriv
        linarith [h2]
      linarith [h_neg]
    have h_iDW2_G_m : iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b) m
        = iteratedDerivWithin 2 F (Icc a b) m := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h_m_lt_b) hG_cdAt_m
            (left_mem_Icc.mpr h_m_lt_b.le)]
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc a_lt_b) hF_cdAt_m h_m_in_Icc]
      have h := iteratedDeriv_comp_const_sub 2 F c
      simp only [neg_one_sq, one_smul] at h
      have := congr_fun h m
      simp only [hcm] at this
      exact this
    have h_iDW3_G_ξ : iteratedDerivWithin 3 (fun t => F (c - t)) (Icc m b) ξ
        = -(iteratedDerivWithin 3 F (Icc a b) (c - ξ)) := by
      have hcξ_ab : c - ξ ∈ Ioo a b := by
        simp only [Set.mem_Ioo]
        constructor
        · linarith [hξ_in.2, hc_def]
        · linarith [hξ_in.1, hcm, h_m_lt_b]
      rw [iteratedDerivWithin_succ]
      have h_hdw_phi : HasDerivWithinAt (fun t => c - t) (-1) (Icc m b) ξ :=
        ((hasDerivAt_id ξ).const_sub c).hasDerivWithinAt
      have h_hdw_g : HasDerivWithinAt (iteratedDerivWithin 2 F (Icc a b))
          (iteratedDerivWithin 3 F (Icc a b) (c - ξ)) (Icc a b) (c - ξ) := by
        rw [iteratedDerivWithin_succ]
        exact ((hF_diff_Ioo (c - ξ) hcξ_ab).differentiableAt
          (Ioo_mem_nhds hcξ_ab.1 hcξ_ab.2)).differentiableWithinAt.hasDerivWithinAt
      have h_hdw_comp : HasDerivWithinAt
          (fun t => iteratedDerivWithin 2 F (Icc a b) (c - t))
          (iteratedDerivWithin 3 F (Icc a b) (c - ξ) * (-1)) (Icc m b) ξ :=
        h_hdw_g.comp ξ h_hdw_phi hφ_maps
      have h_ev_eq : (fun t => iteratedDerivWithin 2 (fun s => F (c - s)) (Icc m b) t)
          =ᶠ[nhdsWithin ξ (Icc m b)]
          (fun t => iteratedDerivWithin 2 F (Icc a b) (c - t)) := by
        apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
        filter_upwards [IsOpen.mem_nhds isOpen_Ioo hξ_in] with y hy
        exact h_iDW2_G_eq y hy
      have h_hdw_iDW2 : HasDerivWithinAt
          (iteratedDerivWithin 2 (fun t => F (c - t)) (Icc m b))
          (iteratedDerivWithin 3 F (Icc a b) (c - ξ) * (-1)) (Icc m b) ξ :=
        h_hdw_comp.congr_of_eventuallyEq h_ev_eq (h_iDW2_G_eq ξ hξ_in)
      rw [h_hdw_iDW2.derivWithin
            (uniqueDiffOn_Icc h_m_lt_b ξ ⟨hξ_in.1.le, hξ_in.2.le⟩)]
      ring
    rw [h_taylEval_G, hGm, hGb, h_deriv_G_m, h_iDW2_G_m, h_iDW3_G_ξ] at hξ_eq
    have h_bm_rel : b - m = -(a - m) := by linarith [hm_def, hc_def]
    have h_bm_sq : (b - m) ^ 2 = (a - m) ^ 2 := by nlinarith [h_bm_rel]
    have h_bm_cu : (b - m) ^ 3 = -((a - m) ^ 3) := by nlinarith [h_bm_rel, h_bm_sq]
    have h_fact : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [show (2 : ℕ) + 1 = 3 from rfl, h_fact] at hξ_eq
    linear_combination hξ_eq
      - (derivWithin F (Icc a b) m) * h_bm_rel
      + (iteratedDerivWithin 2 F (Icc a b) m / 2) * h_bm_sq
      - (iteratedDerivWithin 3 F (Icc a b) (c - ξ) / 6) * h_bm_cu
  obtain ⟨ξ₁, hξ₁_in, hξ₁_eq⟩ := h_taylor_b
  obtain ⟨ξ₂, hξ₂_in, hξ₂_eq⟩ := h_taylor_a
  have h_bm_sq : (b - m) ^ 2 = (a - m) ^ 2 := by
    rw [hm_def]
    ring
  have h_E_expr : E = (iteratedDerivWithin 3 F (Icc a b) ξ₁) * (b - m) ^ 3 / 6 -
                    (iteratedDerivWithin 3 F (Icc a b) ξ₂) * (a - m) ^ 3 / 6 := by
    rw [hE_def]
    have h1 : F b = F m + (derivWithin F (Icc a b) m) * (b - m) +
              (iteratedDerivWithin 2 F (Icc a b) m) * (b - m) ^ 2 / 2 +
              (iteratedDerivWithin 3 F (Icc a b) ξ₁) * (b - m) ^ 3 / 6 := hξ₁_eq
    have h2 : F a = F m + (derivWithin F (Icc a b) m) * (a - m) +
              (iteratedDerivWithin 2 F (Icc a b) m) * (a - m) ^ 2 / 2 +
              (iteratedDerivWithin 3 F (Icc a b) ξ₂) * (a - m) ^ 3 / 6 := hξ₂_eq
    rw [h1, h2]
    rw [h_bm_sq]
    ring
  have h_bm : b - m = (b - a) / 2 := by
    rw [hm_def]
    ring
  have h_am : a - m = -(b - a) / 2 := by
    rw [hm_def]
    ring
  have h_E_simplified : E = ((iteratedDerivWithin 3 F (Icc a b) ξ₁) +
                             (iteratedDerivWithin 3 F (Icc a b) ξ₂)) * (b - a) ^ 3 / 48 := by
    rw [h_E_expr, h_bm, h_am]
    have h1 : (-(b - a) / 2 : ℝ) ^ 3 = -((b - a) ^ 3 / 8) := by
      ring
    rw [h1]
    ring_nf
  have h_pos : 0 < b - a := by linarith [a_lt_b]
  have h_abs_bound : |E| ≤ (|(iteratedDerivWithin 3 F (Icc a b) ξ₁)| +
                           |(iteratedDerivWithin 3 F (Icc a b) ξ₂)|) * (b - a) ^ 3 / 48 := by
    rw [h_E_simplified]
    have h_ba3_nn : (0 : ℝ) ≤ (b - a) ^ 3 := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg h_ba3_nn, abs_of_pos (by norm_num : (0:ℝ) < 48)]
    gcongr
    exact abs_add_le _ _
  have h_fpp_xi1 : |(iteratedDerivWithin 3 F (Icc a b) ξ₁)| ≤ M := by
    apply fpp_bound
  have h_fpp_xi2 : |(iteratedDerivWithin 3 F (Icc a b) ξ₂)| ≤ M := by
    apply fpp_bound
  have h_final_bound : |E| ≤ (b - a) ^ 3 * M / 24 := by
    calc |E| ≤ (|(iteratedDerivWithin 3 F (Icc a b) ξ₁)| +
               |(iteratedDerivWithin 3 F (Icc a b) ξ₂)|) * (b - a) ^ 3 / 48 := h_abs_bound
      _ ≤ (M + M) * (b - a) ^ 3 / 48 := by gcongr
      _ = (b - a) ^ 3 * M / 24 := by ring
  rw [hE_def] at h_final_bound
  exact h_final_bound

/-- The standard error bound for Simpson's midpoint integration on a single interval `[[a, b]]`.

For a function `F` with `F' = f`, if `F` is twice continuously differentiable on `[[a, b]]`,
the second derivative is differentiable on `(a, b)`, and the third derivative is bounded by `M`,
then the midpoint rule error is bounded by `|b - a|^3 * M / 24`. -/
theorem simpson_midpoint_error_le {F : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiffOn ℝ 2 F (uIcc a b))
    (hF_diff : DifferentiableOn ℝ (iteratedDerivWithin 2 F (uIcc a b)) (uIoo a b))
    {M : ℝ} (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (uIcc a b) x| ≤ M) :
    |F b - F a - (derivWithin F (uIcc a b) ((a + b) / 2)) * (b - a)| ≤ |b - a| ^ 3 * M / 24 := by
  rcases lt_trichotomy a b with h_lt | h_eq | h_gt
  · rw [uIcc_of_lt h_lt, uIoo_of_lt h_lt] at *
    rw [abs_of_pos (sub_pos.mpr h_lt)]
    exact simpson_midpoint_error_le_of_lt' h_lt hF hF_diff fpp_bound
  · rw [h_eq]
    simp
  · rw [uIcc_of_gt h_gt, uIoo_of_gt h_gt] at *
    rw [abs_of_neg (sub_neg.mpr h_gt), ← neg_sub a b]
    have h_sum : F b - F a - derivWithin F (Icc b a) ((a + b) / 2) * (-(a - b))
               = F b - F a + derivWithin F (Icc b a) ((a + b) / 2) * (a - b) := by ring
    rw [h_sum]
    have h_abs : |F b - F a + derivWithin F (Icc b a) ((a + b) / 2) * (a - b)|
               = |F a - F b - derivWithin F (Icc b a) ((a + b) / 2) * (a - b)| := by
      have : F b - F a + derivWithin F (Icc b a) ((a + b) / 2) * (a - b)
           = -(F a - F b - derivWithin F (Icc b a) ((a + b) / 2) * (a - b)) := by ring
      rw [this, abs_neg]
    rw [h_abs]
    have h_mid : (a + b) / 2 = (b + a) / 2 := by ring
    rw [h_mid]
    have h_le : |F a - F b - derivWithin F (Icc b a) ((b + a) / 2) * (a - b)| ≤
      (a - b) ^ 3 * M / 24 := simpson_midpoint_error_le_of_lt' h_gt hF hF_diff fpp_bound
    convert h_le using 1
    ring_nf

-- /-- The error bound for Simpson's midpoint integration in the case where `F` is `C^3`.

-- If `F` is three times continuously differentiable on `[[a, b]]` and the third derivative
-- is bounded by `M`, then the midpoint rule error is bounded by `|b - a|^3 * M / 24`. -/
-- theorem simpson_midpoint_error_le_of_c3 {F : ℝ → ℝ} {a b : ℝ}
--     (hF_c3 : ContDiffOn ℝ 3 F (Icc a b)) {M : ℝ}
--     (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
--     |F b - F a - (derivWithin F (Icc a b) ((a + b) / 2)) * (b - a)| ≤ |b - a| ^ 3 * M / 24 := by
--   sorry

-- /-- The composite Simpson's midpoint rule error bound.

-- For `F` with `F' = f`, the error in approximating `∫_a^b f(x) dx` by the midpoint sum
-- `h * ∑_{i=0}^{n-1} f(x_{i+1/2})` is bounded by `(h^2 / 24) * M * |b - a|`
-- where `h = (b-a)/n` and `M` bounds `|F'''|`.

-- Equivalently, since `|b - a| = n * h`, the bound can be written as `(h^2 / 24) * M * (b - a)`. -/
-- theorem simpson_midpoint_composite_error_le {F : ℝ → ℝ} {a b : ℝ} {N : ℕ} (N_nonzero : 0 < N)
--     (hF_c3 : ContDiffOn ℝ 3 F (Icc a b)) {M : ℝ}
--     (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
--     let h := (b - a) / N
--     |simpson_midpoint_error F N a b| ≤ (h ^ 2 / 24) * M * |b - a| := by
--   sorry

end
