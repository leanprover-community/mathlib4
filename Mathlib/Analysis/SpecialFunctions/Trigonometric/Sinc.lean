/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Sinc function

This file contains the definition of the sinc function and some of its properties.

## Main definitions

* `Real.sinc`: the (unnormalized) sinc function, defined as `sinc x = sin x / x` for `x ≠ 0`
  and `1` for `x = 0`.

## Main statements

* `continuous_sinc`: the sinc function is continuous.
* `cos_le_sinc`: `cos x ≤ sinc x` for `|x| < π / 2`; together with `sinc_le_one` this is the
  classical squeeze behind the limit of `sin x / x` at `0`
  (`Real.tendsto_sin_div_nhdsNE_zero`, proved in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean`).
* `sinc_pos`: `sinc` is positive on `(-π, π)`.

-/

@[expose] public section

open scoped Topology

namespace Real

variable {x : ℝ}

/-- The function `sin x / x` modified to take the value 1 at 0, which makes it continuous. -/
@[pp_nodot]
noncomputable def sinc (x : ℝ) : ℝ := if x = 0 then 1 else sin x / x

lemma sinc_apply : sinc x = if x = 0 then 1 else sin x / x := rfl

@[simp]
lemma sinc_zero : sinc 0 = 1 := by simp [sinc]

lemma sinc_of_ne_zero (hx : x ≠ 0) : sinc x = sin x / x := by simp [sinc, hx]

lemma sinc_eq_dslope : sinc = dslope sin 0 := by
  ext
  simp [dslope, Function.update_apply, sinc, slope, div_eq_inv_mul]

@[simp]
lemma sinc_neg (x : ℝ) : sinc (-x) = sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sinc_of_ne_zero hx, sinc_of_ne_zero (neg_ne_zero.mpr hx)]

lemma abs_sinc_le_one (x : ℝ) : |sinc x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [sinc_of_ne_zero hx, abs_div]
  refine div_le_of_le_mul₀ (abs_nonneg _) zero_le_one ?_
  rw [one_mul]
  exact abs_sin_le_abs

lemma sinc_le_one (x : ℝ) : sinc x ≤ 1 := (abs_le.mp (abs_sinc_le_one x)).2

lemma neg_one_le_sinc (x : ℝ) : -1 ≤ sinc x := (abs_le.mp (abs_sinc_le_one x)).1

lemma sin_div_le_inv_abs (x : ℝ) : sin x / x ≤ |x|⁻¹ := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_nonpos hx.le, ← one_div, le_div_iff₀, div_eq_mul_inv]
    · ring_nf
      rw [mul_assoc, mul_inv_cancel₀ hx.ne, mul_one, neg_le]
      exact neg_one_le_sin x
    · simpa using hx
  · simp
  · rw [abs_of_nonneg hx.le, div_eq_mul_inv, mul_inv_le_iff₀ hx, inv_mul_cancel₀ hx.ne']
    exact sin_le_one x

lemma sinc_le_inv_abs (hx : x ≠ 0) : sinc x ≤ |x|⁻¹ := by
  rw [sinc_of_ne_zero hx]
  exact sin_div_le_inv_abs x

/-- The function `sinc` is continuous. -/
@[fun_prop]
lemma continuous_sinc : Continuous sinc := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  rw [sinc_eq_dslope]
  by_cases hx : x = 0
  · simp [hx]
  · rw [continuousAt_dslope_of_ne hx]
    fun_prop

/-- **Squeeze bound for `sinc`.** For `|x| < π / 2` we have `cos x ≤ sinc x`; together with
`sinc_le_one` this is the classical squeeze `cos x ≤ sin x / x ≤ 1`. -/
lemma cos_le_sinc (hx : |x| < π / 2) : cos x ≤ sinc x := by
  wlog hx₀ : 0 ≤ x generalizing x
  · simpa using this (x := -x) (by simpa using hx) (by linarith [not_le.mp hx₀])
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp
  have hx' := (abs_lt.mp hx).2
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hx'⟩
  rw [sinc_of_ne_zero hx₀.ne', le_div_iff₀ hx₀, ← tan_mul_cos hc.ne', mul_comm]
  exact mul_le_mul_of_nonneg_right (le_tan hx₀.le hx') hc.le

/-- The function `sinc` is positive on `(-π, π)`. -/
lemma sinc_pos (hx : |x| < π) : 0 < sinc x := by
  wlog hx₀ : 0 ≤ x generalizing x
  · simpa using this (x := -x) (by simpa using hx) (by linarith [not_le.mp hx₀])
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp
  rw [sinc_of_ne_zero hx₀.ne']
  exact div_pos (sin_pos_of_pos_of_lt_pi hx₀ (abs_lt.mp hx).2) hx₀

end Real
