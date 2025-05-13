/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Sinc function

This file contains the definition of the sinc function and some of its properties.

## Main definitions

* `Real.sinc`: the sinc function, defined as `sinc x = sin x / x` for `x ≠ 0` and `1` for `x = 0`.

## Main statements

* `continuous_sinc`: the sinc function is continuous.

-/

open Filter
open scoped Topology

namespace Real

variable {x : ℝ}

/-- The function `sin x / x` mofified to take the value 1 at 0, which makes it continuous. -/
@[pp_nodot]
noncomputable def sinc (x : ℝ) : ℝ := if x = 0 then 1 else sin x / x

lemma sinc_apply : sinc x = if x = 0 then 1 else sin x / x := rfl

@[simp]
lemma sinc_zero : sinc 0 = 1 := by simp [sinc]

lemma sinc_of_ne_zero (hx : x ≠ 0) : sinc x = sin x / x := by simp [sinc, hx]

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

/-- For `0 < x ≤ 1` we have `1 - x ^ 2 / 4 < sinc x`.
This is not tight and could be extended to `1 < x`: see `sin_gt_sub_cube`. -/
lemma sinc_gt_sub_sq' (h : 0 < x) (h' : x ≤ 1) : 1 - x ^ 2 / 4 < sinc x := by
  rw [sinc_of_ne_zero h.ne', lt_div_iff₀ h]
  convert sin_gt_sub_cube h h' using 1
  ring

/-- For `|x| ≤ 1` we have `1 - x ^ 2 / 4 ≤ sinc x`.
This is not tight and could be extended to `1 < |x|`: see `sin_gt_sub_cube`. -/
lemma sinc_ge_sub_sq (h : |x| ≤ 1) : 1 - x ^ 2 / 4 ≤ sinc x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [← sinc_neg x]
    rw [abs_of_neg hx] at h
    convert (sinc_gt_sub_sq' (neg_pos.mpr hx) h).le using 1
    ring
  · simp
  · rw [abs_of_nonneg hx.le] at h
    exact (sinc_gt_sub_sq' hx h).le

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
  by_cases hx : x = 0
  · subst hx
    refine continuousAt_of_tendsto_nhds (y := 1) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun x ↦ 1 - x^2 / 4) (h := fun _ ↦ 1)
      ?_ tendsto_const_nhds ?_ (.of_forall fun x ↦ ?_)
    · nth_rw 2 [← sub_zero (1 : ℝ), ← zero_div (4 : ℝ), ← zero_pow (n := 2) (by simp)]
      exact tendsto_const_nhds.sub ((tendsto_id.pow 2).div tendsto_const_nhds (by simp))
    · have : ∀ᶠ x in 𝓝 (0 : ℝ), |x| ≤ 1 := by
        filter_upwards [eventually_le_nhds zero_lt_one,
          eventually_ge_nhds (by simp : (-1 : ℝ) < 0)] with x hx_lt hx_ge
        exact abs_le.mpr ⟨hx_ge, hx_lt⟩
      filter_upwards [this] with x hx using sinc_ge_sub_sq hx
    · exact sinc_le_one x
  · suffices ContinuousAt (fun x ↦ sin x / x) x by
      refine this.congr ?_
      filter_upwards [eventually_ne_nhds hx] with y hy using by rw [sinc_of_ne_zero hy]
    exact continuous_sin.continuousAt.div continuous_id.continuousAt hx

end Real
