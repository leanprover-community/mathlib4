/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Polynomial bounds for trigonometric functions

## Main statements

This file contains upper and lower bounds for real trigonometric functions in terms
of polynomials. See `Trigonometric.Basic` for more elementary inequalities, establishing
the ranges of these functions, and their monotonicity in suitable intervals.

Here we prove the following:

* `sin_lt`: for `x > 0` we have `sin x < x`.
* `sin_gt_sub_cube`: For `0 < x ≤ 1` we have `x - x ^ 3 / 4 < sin x`.
* `lt_tan`: for `0 < x < π/2` we have `x < tan x`.
* `cos_le_one_div_sqrt_sq_add_one` and `cos_lt_one_div_sqrt_sq_add_one`: for
  `-3 * π / 2 ≤ x ≤ 3 * π / 2`, we have `cos x ≤ 1 / sqrt (x ^ 2 + 1)`, with strict inequality if
  `x ≠ 0`. (This bound is not quite optimal, but not far off)

## Tags

sin, cos, tan, angle
-/

open Set

namespace Real
variable {x : ℝ}

/-- For 0 < x, we have sin x < x. -/
theorem sin_lt (h : 0 < x) : sin x < x := by
  rcases lt_or_ge 1 x with h' | h'
  · exact (sin_le_one x).trans_lt h'
  have hx : |x| = x := abs_of_nonneg h.le
  have := le_of_abs_le (sin_bound <| show |x| ≤ 1 by rwa [hx])
  rw [sub_le_iff_le_add', hx] at this
  apply this.trans_lt
  rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
  refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
  apply pow_le_pow_of_le_one h.le h'
  simp

lemma sin_le (hx : 0 ≤ x) : sin x ≤ x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (sin_lt hx).le

lemma lt_sin (hx : x < 0) : x < sin x := by simpa using sin_lt <| neg_pos.2 hx
lemma le_sin (hx : x ≤ 0) : x ≤ sin x := by simpa using sin_le <| neg_nonneg.2 hx

theorem lt_sin_mul {x : ℝ} (hx : 0 < x) (hx' : x < 1) : x < sin (π / 2 * x) := by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.2 ⟨le_rfl, pi_pos.le⟩ ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩
      pi_div_two_pos.ne (sub_pos.2 hx') hx

theorem le_sin_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : x ≤ sin (π / 2 * x) := by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, pi_pos.le⟩
      ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ (sub_nonneg.2 hx') hx

theorem mul_lt_sin {x : ℝ} (hx : 0 < x) (hx' : x < π / 2) : 2 / π * x < sin x := by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @lt_sin_mul ((π / 2)⁻¹ * x)
    (mul_pos (inv_pos.2 pi_div_two_pos) hx) (by rwa [← div_eq_inv_mul, div_lt_one pi_div_two_pos])

/-- One half of **Jordan's inequality**.

In the range `[0, π / 2]`, we have a linear lower bound on `sin`. The other half is given by
`Real.sin_le`.
-/
theorem mul_le_sin {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) : 2 / π * x ≤ sin x := by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @le_sin_mul ((π / 2)⁻¹ * x)
    (mul_nonneg (inv_nonneg.2 pi_div_two_pos.le) hx)
    (by rwa [← div_eq_inv_mul, div_le_one pi_div_two_pos])

/-- Half of **Jordan's inequality** for negative values. -/
lemma sin_le_mul (hx : -(π / 2) ≤ x) (hx₀ : x ≤ 0) : sin x ≤ 2 / π * x := by
  simpa using mul_le_sin (neg_nonneg.2 hx₀) (neg_le.2 hx)

/-- Half of **Jordan's inequality** for absolute values. -/
lemma mul_abs_le_abs_sin (hx : |x| ≤ π / 2) : 2 / π * |x| ≤ |sin x| := by
  wlog hx₀ : 0 ≤ x
  case inr => simpa using this (by rwa [abs_neg]) <| neg_nonneg.2 <| le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx ⊢
  exact (mul_le_sin hx₀ hx).trans (le_abs_self _)

lemma sin_sq_lt_sq (hx : x ≠ 0) : sin x ^ 2 < x ^ 2 := by
  wlog hx₀ : 0 < x
  case inr =>
    simpa using this (neg_ne_zero.2 hx) <| neg_pos_of_neg <| hx.lt_of_le <| le_of_not_gt hx₀
  rcases le_or_gt x 1 with hxπ | hxπ
  case inl =>
    exact pow_lt_pow_left₀ (sin_lt hx₀)
      (sin_nonneg_of_nonneg_of_le_pi hx₀.le (by linarith [two_le_pi])) (by simp)
  case inr =>
    exact (sin_sq_le_one _).trans_lt (by rwa [one_lt_sq_iff₀ hx₀.le])

lemma sin_sq_le_sq : sin x ^ 2 ≤ x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (sin_sq_lt_sq hx).le

lemma abs_sin_lt_abs (hx : x ≠ 0) : |sin x| < |x| := sq_lt_sq.1 (sin_sq_lt_sq hx)
lemma abs_sin_le_abs : |sin x| ≤ |x| := sq_le_sq.1 sin_sq_le_sq

lemma one_sub_sq_div_two_lt_cos (hx : x ≠ 0) : 1 - x ^ 2 / 2 < cos x := by
  have := (sin_sq_lt_sq (by positivity)).trans_eq' (sin_sq_eq_half_sub (x / 2)).symm
  ring_nf at this
  linarith

lemma one_sub_sq_div_two_le_cos : 1 - x ^ 2 / 2 ≤ cos x := by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (one_sub_sq_div_two_lt_cos hx).le

/-- Half of **Jordan's inequality** for `cos`. -/
lemma one_sub_mul_le_cos (hx₀ : 0 ≤ x) (hx : x ≤ π / 2) : 1 - 2 / π * x ≤ cos x := by
  simpa [sin_pi_div_two_sub, mul_sub, div_mul_div_comm, mul_comm π, pi_pos.ne']
    using mul_le_sin (x := π / 2 - x) (by simpa) (by simpa)

/-- Half of **Jordan's inequality** for `cos` and negative values. -/
lemma one_add_mul_le_cos (hx₀ : -(π / 2) ≤ x) (hx : x ≤ 0) : 1 + 2 / π * x ≤ cos x := by
  simpa using one_sub_mul_le_cos (x := -x) (by linarith) (by linarith)

lemma cos_le_one_sub_mul_cos_sq (hx : |x| ≤ π) : cos x ≤ 1 - 2 / π ^ 2 * x ^ 2 := by
  wlog hx₀ : 0 ≤ x
  case inr => simpa using this (by rwa [abs_neg]) <| neg_nonneg.2 <| le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx
  have : x / π ≤ sin (x / 2) := by simpa using mul_le_sin (x := x / 2) (by positivity) (by linarith)
  have := (pow_le_pow_left₀ (by positivity) this 2).trans_eq (sin_sq_eq_half_sub _)
  ring_nf at this ⊢
  linarith

/-- For 0 < x ≤ 1 we have x - x ^ 3 / 4 < sin x.

This is also true for x > 1, but it's nontrivial for x just above 1. This inequality is not
tight; the tighter inequality is sin x > x - x ^ 3 / 6 for all x > 0, but this inequality has
a simpler proof. -/
theorem sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : x - x ^ 3 / 4 < sin x := by
  have hx : |x| = x := abs_of_nonneg h.le
  have := neg_le_of_abs_le (sin_bound <| show |x| ≤ 1 by rwa [hx])
  rw [le_sub_iff_add_le, hx] at this
  refine lt_of_lt_of_le ?_ this
  have : x ^ 3 / ↑4 - x ^ 3 / ↑6 = x ^ 3 * 12⁻¹ := by norm_num [div_eq_mul_inv, ← mul_sub]
  rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left, ← lt_sub_iff_add_lt', this]
  refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
  apply pow_le_pow_of_le_one h.le h'
  simp

/-- The derivative of `tan x - x` is `1/(cos x)^2 - 1` away from the zeroes of cos. -/
theorem deriv_tan_sub_id (x : ℝ) (h : cos x ≠ 0) :
    deriv (fun y : ℝ => tan y - y) x = 1 / cos x ^ 2 - 1 :=
  HasDerivAt.deriv <| by simpa using (hasDerivAt_tan h).add (hasDerivAt_id x).neg

/-- For all `0 < x < π/2` we have `x < tan x`.

This is proved by checking that the function `tan x - x` vanishes
at zero and has non-negative derivative. -/
theorem lt_tan {x : ℝ} (h1 : 0 < x) (h2 : x < π / 2) : x < tan x := by
  let U := Ico 0 (π / 2)
  have intU : interior U = Ioo 0 (π / 2) := interior_Ico
  have half_pi_pos : 0 < π / 2 := div_pos pi_pos two_pos
  have cos_pos {y : ℝ} (hy : y ∈ U) : 0 < cos y := by
    exact cos_pos_of_mem_Ioo (Ico_subset_Ioo_left (neg_lt_zero.mpr half_pi_pos) hy)
  have sin_pos {y : ℝ} (hy : y ∈ interior U) : 0 < sin y := by
    rw [intU] at hy
    exact sin_pos_of_mem_Ioo (Ioo_subset_Ioo_right (div_le_self pi_pos.le one_le_two) hy)
  have tan_cts_U : ContinuousOn tan U := by
    apply ContinuousOn.mono continuousOn_tan
    intro z hz
    simp only [mem_setOf_eq]
    exact (cos_pos hz).ne'
  have tan_minus_id_cts : ContinuousOn (fun y : ℝ => tan y - y) U := tan_cts_U.sub continuousOn_id
  have deriv_pos (y : ℝ) (hy : y ∈ interior U) : 0 < deriv (fun y' : ℝ => tan y' - y') y := by
    have := cos_pos (interior_subset hy)
    simp only [deriv_tan_sub_id y this.ne', one_div, gt_iff_lt, sub_pos]
    norm_cast
    have bd2 : cos y ^ 2 < 1 := by
      apply lt_of_le_of_ne y.cos_sq_le_one
      rw [cos_sq']
      simpa only [Ne, sub_eq_self, sq_eq_zero_iff] using (sin_pos hy).ne'
    rwa [lt_inv_comm₀, inv_one]
    · exact zero_lt_one
    simpa only [sq, mul_self_pos] using this.ne'
  have mono := strictMonoOn_of_deriv_pos (convex_Ico 0 (π / 2)) tan_minus_id_cts deriv_pos
  have zero_in_U : (0 : ℝ) ∈ U := by rwa [left_mem_Ico]
  have x_in_U : x ∈ U := ⟨h1.le, h2⟩
  simpa only [tan_zero, sub_zero, sub_pos] using mono zero_in_U x_in_U h1

theorem le_tan {x : ℝ} (h1 : 0 ≤ x) (h2 : x < π / 2) : x ≤ tan x := by
  rcases eq_or_lt_of_le h1 with (rfl | h1')
  · rw [tan_zero]
  · exact le_of_lt (lt_tan h1' h2)

theorem cos_lt_one_div_sqrt_sq_add_one {x : ℝ} (hx1 : -(3 * π / 2) ≤ x) (hx2 : x ≤ 3 * π / 2)
    (hx3 : x ≠ 0) : cos x < (1 / √(x ^ 2 + 1) : ℝ) := by
  suffices ∀ {y : ℝ}, 0 < y → y ≤ 3 * π / 2 → cos y < 1 / √(y ^ 2 + 1) by
    rcases lt_or_lt_iff_ne.mpr hx3.symm with ⟨h⟩
    · exact this h hx2
    · convert this (by linarith : 0 < -x) (by linarith) using 1
      · rw [cos_neg]
      · rw [neg_sq]
  intro y hy1 hy2
  have hy3 : ↑0 < y ^ 2 + 1 := by linarith [sq_nonneg y]
  rcases lt_or_ge y (π / 2) with (hy2' | hy1')
  · -- Main case : `0 < y < π / 2`
    have hy4 : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith, hy2'⟩
    rw [← abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith, hy2'.le⟩), ←
      abs_of_nonneg (one_div_nonneg.mpr (sqrt_nonneg _)), ← sq_lt_sq, div_pow, one_pow,
      sq_sqrt hy3.le, lt_one_div (pow_pos hy4 _) hy3, ← inv_one_add_tan_sq hy4.ne', one_div,
      inv_inv, add_comm, add_lt_add_iff_left, sq_lt_sq, abs_of_pos hy1,
      abs_of_nonneg (tan_nonneg_of_nonneg_of_le_pi_div_two hy1.le hy2'.le)]
    exact Real.lt_tan hy1 hy2'
  · -- Easy case : `π / 2 ≤ y ≤ 3 * π / 2`
    refine lt_of_le_of_lt ?_ (one_div_pos.mpr <| sqrt_pos_of_pos hy3)
    exact cos_nonpos_of_pi_div_two_le_of_le hy1' (by linarith [pi_pos])

theorem cos_le_one_div_sqrt_sq_add_one {x : ℝ} (hx1 : -(3 * π / 2) ≤ x) (hx2 : x ≤ 3 * π / 2) :
    cos x ≤ (1 : ℝ) / √(x ^ 2 + 1) := by
  rcases eq_or_ne x 0 with (rfl | hx3)
  · simp
  · exact (cos_lt_one_div_sqrt_sq_add_one hx1 hx2 hx3).le

theorem norm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖.exp (.I * x) - (1 : ℂ)‖ ≤ ‖x‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    _ = 2 * |Real.sin (x / 2)| := by simp
    _ ≤ 2 * |x / 2| := (mul_le_mul_iff_of_pos_left zero_lt_two).mpr Real.abs_sin_le_abs
    _ = _ := by rw [abs_div, Nat.abs_ofNat, Real.norm_eq_abs]; ring

theorem enorm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖.exp (.I * x) - (1 : ℂ)‖ₑ ≤ ‖x‖ₑ := by
  iterate 2 rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal norm_exp_I_mul_ofReal_sub_one_le

theorem nnnorm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖.exp (.I * x) - (1 : ℂ)‖₊ ≤ ‖x‖₊ := by
  rw [← ENNReal.coe_le_coe]; exact enorm_exp_I_mul_ofReal_sub_one_le

end Real
