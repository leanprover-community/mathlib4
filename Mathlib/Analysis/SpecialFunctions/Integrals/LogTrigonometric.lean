/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-!
# Integral of `log ∘ sin`

This file computes special values of the integral of `log ∘ sin`. Given that the indefinite integral
involves the dilogarithm, this can be seen as computing special values of `Li₂`.
-/

open Filter Interval Real

/-
Helper lemma for `integral_log_sin_zero_pi_div_two`: The integral of `log ∘ sin` on `0 … π` is
double the integral on `0 … π/2`.
-/
private lemma integral_log_sin_zero_pi_eq_two_mul_integral_log_sin_zero_pi_div_two :
    ∫ x in (0)..π, log (sin x) = 2 * ∫ x in (0)..(π / 2), log (sin x) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := π / 2) (c := π)
    (by apply intervalIntegrable_log_sin) (by apply intervalIntegrable_log_sin)]
  conv =>
    left; right; arg 1
    intro x
    rw [← sin_pi_sub]
  rw [intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)), sub_self,
    (by linarith : π - π / 2 = π / 2)]
  ring!

/--
The integral of `log ∘ sin` on `0 … π/2` equals `-log 2 * π / 2`.
-/
theorem integral_log_sin_zero_pi_div_two : ∫ x in (0)..(π / 2), log (sin x) = -log 2 * π / 2 := by
  calc ∫ x in (0)..(π / 2), log (sin x)
    _ = ∫ x in (0)..(π / 2), (log (sin (2 * x)) - log 2 - log (cos x)) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      apply Filter.codiscreteWithin.mono (by tauto : Ι 0 (π / 2) ⊆ Set.univ)
      have t₀ : sin ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
        apply analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := π / 2)
        simp
      have t₁ : cos ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ := by
        apply analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0)
        simp
      filter_upwards [t₀, t₁] with y h₁y h₂y
      simp_all only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        sin_two_mul, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, log_mul]
      ring
    _ = (∫ x in (0)..(π / 2), log (sin (2 * x))) - π / 2 * log 2
        - ∫ x in (0)..(π / 2), log (cos x) := by
      rw [intervalIntegral.integral_sub _ _,
        intervalIntegral.integral_sub _ intervalIntegrable_const,
        intervalIntegral.integral_const]
      · simp
      · simpa using (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left
      · apply IntervalIntegrable.sub _ intervalIntegrable_const
        simpa using (intervalIntegrable_log_sin (a := 0) (b := π)).comp_mul_left
      · exact intervalIntegrable_log_cos
    _ = (∫ x in (0)..(π / 2), log (sin (2 * x)))
        - π / 2 * log 2 - ∫ x in (0)..(π / 2), log (sin x) := by
      simp [← sin_pi_div_two_sub,
        intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)) (π / 2)]
    _ = -log 2 * π / 2 := by
      simp only [intervalIntegral.integral_comp_mul_left (f := fun x ↦ log (sin x)) two_ne_zero,
        mul_zero, (by linarith : 2 * (π / 2) = π),
        integral_log_sin_zero_pi_eq_two_mul_integral_log_sin_zero_pi_div_two, smul_eq_mul, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel_left₀, sub_sub_cancel_left, neg_mul]
      linarith

/--
The integral of `log ∘ sin` on `0 … π` equals `-log 2 * π`.
-/
theorem integral_log_sin_zero_pi : ∫ x in (0)..π, log (sin x) = -log 2 * π := by
  rw [integral_log_sin_zero_pi_eq_two_mul_integral_log_sin_zero_pi_div_two,
    integral_log_sin_zero_pi_div_two]
  ring
