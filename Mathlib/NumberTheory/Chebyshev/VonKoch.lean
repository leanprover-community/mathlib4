/-
Copyright (c) 2026 Zhuoyuan Hao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoyuan Hao
-/
module

public import Mathlib.NumberTheory.Chebyshev

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Von Koch's prime-counting error from the Chebyshev bound

Abel summation transfers a square-root error bound for the Chebyshev function
to the difference between the prime-counting function and the logarithmic integral.
-/

public section

open Asymptotics Filter MeasureTheory Set Real
open scoped Chebyshev Nat.Prime

namespace Chebyshev

/-- A von Koch error bound for `ψ` gives the same bound for `θ`. -/
theorem isBigO_theta_sub_id_of_psi_sub_id
    (hψ : (fun x ↦ ψ x - x) =O[atTop] fun x ↦ √x * log x ^ 2) :
    (fun x ↦ θ x - x) =O[atTop] fun x ↦ √x * log x ^ 2 := by
  have h : sqrt =O[atTop] fun x ↦ √x * log x ^ 2 := by
    apply IsBigO.of_bound'
    filter_upwards [tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _), abs_mul, abs_sq] using
      le_mul_of_one_le_right (sqrt_nonneg x) (one_le_pow₀ hx : 1 ≤ log x ^ 2)
  simpa only [Pi.sub_apply, sub_sub_sub_cancel_left] using
    hψ.sub (isBigO_psi_sub_theta_sqrt.trans h)

private lemma li_parts (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, 1 / log t) - (∫ t in (2 : ℝ)..x, 1 / log t ^ 2) =
      x / log x - 2 / log 2 := by
  have hB := intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x)
  have hA : IntervalIntegrable (fun t : ℝ ↦ 1 / log t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hx fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    fun_prop
  rw [← intervalIntegral.integral_sub hA hB]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ t / log t) _ (hA.sub hB)
  intro t ht
  rw [uIcc_of_le hx] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  apply ((hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hl).congr_deriv
  simp only [id_eq]
  field_simp

private noncomputable def countingKernel (t : ℝ) : ℝ := θ t / (t * log t ^ 2) - 1 / log t ^ 2

private lemma integral_countingKernel_le {a x C : ℝ} (ha : 2 ≤ a) (hx : a ≤ x) (hC : 0 ≤ C)
    (hint : IntervalIntegrable countingKernel volume a x)
    (hθ : ∀ t ≥ a, |θ t - t| ≤ C * (√t * log t ^ 2)) :
    |∫ t in a..x, countingKernel t| ≤ 2 * C * √x := by
  have hR : IntervalIntegrable (fun t : ℝ ↦ C / √t) volume a x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hx fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have hs : √t ≠ 0 := (sqrt_pos.2 (by linarith [ht.1])).ne'
    fun_prop
  calc
    _ ≤ ∫ t in a..x, |countingKernel t| := intervalIntegral.abs_integral_le_integral_abs hx
    _ ≤ ∫ t in a..x, C / √t := by
      apply intervalIntegral.integral_mono_on hx hint.abs hR
      intro t ht
      have ht₀ : 0 < t := by linarith [ht.1]
      have hl : 0 < log t := log_pos (by linarith [ht.1])
      have he : countingKernel t = (θ t - t) / (t * log t ^ 2) := by
        dsimp [countingKernel]
        field_simp
      change |countingKernel t| ≤ C / √t
      rw [he, abs_div, abs_of_pos (mul_pos ht₀ (sq_pos_of_pos hl)),
        div_le_div_iff₀ (by positivity) (sqrt_pos.2 ht₀)]
      calc |θ t - t| * √t ≤ (C * (√t * log t ^ 2)) * √t := by gcongr; exact hθ t ht.1
        _ = _ := by linear_combination C * log t ^ 2 * sq_sqrt ht₀.le
    _ = 2 * C * √x - 2 * C * √a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ 2 * C * √t) _ hR
      intro t ht
      rw [uIcc_of_le hx] at ht
      have ht₀ : 0 < t := by linarith [ht.1]
      have hs := (sqrt_pos.2 ht₀).ne'
      convert (hasDerivAt_sqrt ht₀.ne').const_mul (2 * C) using 1
      field_simp
    _ ≤ _ := sub_le_self _ (by positivity)

/-- Abel summation transfers the von Koch bound for `θ` to the prime-counting function,
with the logarithmic integral normalized to vanish at two. -/
theorem isBigO_primeCounting_sub_integral_of_theta_sub_id
    (hθ : (fun x ↦ θ x - x) =O[atTop] fun x ↦ √x * log x ^ 2) :
    (fun x ↦ (π ⌊x⌋₊ : ℝ) - ∫ t in 2..x, 1 / log t) =O[atTop] fun x ↦ √x * log x := by
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.1 hθ
  obtain ⟨a, h⟩ := eventually_atTop.1 (hbound.and (eventually_ge_atTop 2))
  have ha := (h a le_rfl).2
  have hθ (t : ℝ) (ht : a ≤ t) := (h t ht).1
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sqrt_nonneg _) (sq_nonneg _))] at hθ
  let B := |(∫ t in 2..a, countingKernel t) + 2 / log 2|
  apply IsBigO.of_bound (3 * C + B)
  filter_upwards [eventually_ge_atTop a, tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  have hx₂ := ha.trans hx
  have hL₀ : 0 < log x := by linarith
  have hS : 1 ≤ √x := by simpa using sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ x)
  have hT := (intervalIntegrable_iff_integrableOn_Icc_of_le hx₂).2
    (integrableOn_theta_div_id_mul_log_sq x)
  have hB := intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x)
  have ⟨hl, hr⟩ := (IntervalIntegrable.trans_iff (b := a) (f := countingKernel)
    (by simpa [uIcc_of_le hx₂] using And.intro ha hx)).mp (hT.sub hB)
  have hEnd : |(θ x - x) / log x| ≤ C * (√x * log x) := by
    rw [abs_div, abs_of_pos hL₀, div_le_iff₀ hL₀]
    simpa only [sq, mul_assoc] using hθ x hx
  have hid : (π ⌊x⌋₊ : ℝ) - (∫ t in 2..x, 1 / log t) =
      (θ x - x) / log x + (∫ t in a..x, countingKernel t) +
        ((∫ t in 2..a, countingKernel t) + 2 / log 2) := by
    rw [add_assoc, add_left_comm (∫ t in a..x, _), ← add_assoc (∫ t in 2..a, _),
      intervalIntegral.integral_add_adjacent_intervals hl hr]
    simp only [countingKernel, intervalIntegral.integral_sub hT hB,
      primeCounting_eq_theta_div_log_add_integral hx₂, sub_div]
    linarith only [li_parts x hx₂]
  rw [Real.norm_eq_abs, hid, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ √x * log x)]
  calc
    _ ≤ |(θ x - x) / log x| + |∫ t in a..x, countingKernel t| + B :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C * (√x * log x) + 2 * C * √x + B := by
      linarith only [hEnd, integral_countingKernel_le ha hx hC.le hr hθ]
    _ ≤ _ := by
      nlinarith only [mul_nonneg (mul_nonneg hC.le (sqrt_nonneg x)) (sub_nonneg.mpr hL),
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hS hL) (abs_nonneg _ : 0 ≤ B)]

/-- The von Koch bound for `ψ` implies the prime-counting error `O(√x * log x)`. -/
theorem isBigO_primeCounting_sub_integral_of_psi_sub_id
    (hψ : (fun x ↦ ψ x - x) =O[atTop] fun x ↦ √x * log x ^ 2) :
    (fun x ↦ (π ⌊x⌋₊ : ℝ) - ∫ t in 2..x, 1 / log t) =O[atTop] fun x ↦ √x * log x :=
  isBigO_primeCounting_sub_integral_of_theta_sub_id (isBigO_theta_sub_id_of_psi_sub_id hψ)

end Chebyshev
