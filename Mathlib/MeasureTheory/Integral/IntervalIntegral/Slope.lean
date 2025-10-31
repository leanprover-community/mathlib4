/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Some properties of the interval integral of `fun x ↦ slope f x (x + c)`, given a constant `c : ℝ`

This file proves that:
* `IntervalIntegrable.intervalIntegrable_slope`: If `f` is interval integrable on `a..(b + c)`
where `a ≤ b` and `0 ≤ c`, then `fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.
* `MonotoneOn.intervalIntegrable_slope` - If `f` is monotone on `a..(b + c)`
where `a ≤ b` and `0 ≤ c`, then `fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.
* `MonotoneOn.intervalIntegral_slope_bound` -  If `f` is monotone on `a..(b + c)`
where `a ≤ b` and `0 ≤ c`, then the interval integral of `fun x ↦ slope f x (x + c)` on `a..b` is
at most `f (b + c) - f a`.

## Tags
interval integrable, interval integral, monotone, slope
-/

open MeasureTheory Set

/-- If `f` is interval integrable on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then
`fun x ↦ slope f x (x + c)` is interval integrable on `a..b`. -/
theorem IntervalIntegrable.intervalIntegrable_slope {f : ℝ → ℝ} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a (b + c)) (hab : a ≤ b) (hc : 0 ≤ c) :
    IntervalIntegrable (fun x ↦ slope f x (x + c)) volume a b := by
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
  exact hf.comp_add_right c |>.mono_set (by grind [uIcc]) |>.sub (hf.mono_set (by grind [uIcc]))
    |>.const_mul (c := c⁻¹)

/-- If `f` is monotone on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then
`fun x ↦ slope f x (x + c)` is interval integrable on `a..b`. -/
theorem MonotoneOn.intervalIntegrable_slope {f : ℝ → ℝ} {a b c : ℝ}
    (hf : MonotoneOn f (Icc a (b + c))) (hab : a ≤ b) (hc : 0 ≤ c) :
    IntervalIntegrable (fun x ↦ slope f x (x + c)) volume a b :=
  uIcc_of_le (show a ≤ b + c by linarith) ▸ hf |>.intervalIntegrable.intervalIntegrable_slope hab hc

/-- If `f` is monotone on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then the interval integral of
`fun x ↦ slope f x (x + c)` on `a..b` is at most `f (b + c) - f a`. -/
theorem MonotoneOn.intervalIntegral_slope_le {f : ℝ → ℝ} {a b c : ℝ}
    (hf : MonotoneOn f (Icc a (b + c))) (hab : a ≤ b) (hc : 0 ≤ c) :
    ∫ x in a..b, slope f x (x + c) ≤ f (b + c) - f a := by
  rcases eq_or_lt_of_le hc with hc | hc
  · simp only [← hc, add_zero, slope_same, intervalIntegral.integral_zero, sub_nonneg]
    apply hf <;> grind
  rw [← uIcc_of_le (by linarith)] at hf
  have hf' := hf.intervalIntegrable (μ := volume)
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub
        (hf'.comp_add_right c |>.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc])),
      intervalIntegral.integral_comp_add_right,
      intervalIntegral.integral_interval_sub_interval_comm'
        (hf'.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc]))]
  have fU : ∫ (x : ℝ) in b..b + c, f x ≤ c * f (b + c) := by
    grw [intervalIntegral.integral_mono_on (g := fun _ ↦ f (b + c))
          (by linarith)
          (hf'.mono_set (by grind [uIcc]))
          (by simp)
          (by intros; apply hf <;> grind [uIcc])]
    simp
  have fL : c * f a ≤ ∫ (x : ℝ) in a..a + c, f x := by
    grw [← intervalIntegral.integral_mono_on (f := fun _ ↦ f a)
            (by linarith)
            (by simp)
            (hf'.mono_set (by grind [uIcc]))
            (by intros; apply hf <;> grind [uIcc])]
    simp
  grw [fU, ← fL]
  field_simp; rfl
