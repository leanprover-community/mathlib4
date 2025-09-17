/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Representation of `log⁺` as a Circle Average

If `a` is any complex number of norm one, then `log ‖· - a‖` is circle integrable over every circle
in the complex plane, and the circle average `circleAverage (log ‖· - a‖) 0 1` vanishes.

- Integrability is recalled in `circleIntegrability_log_norm_id_sub_const`, as a consequence of the
  general fact that functions of the form `log ‖meromorphic‖` are circle integrable.

- The value of the integral is computed in `circleAverage_log_norm_id_sub_const₁`.

TODO: As soon as the mean value theorem for harmonic functions becomes available, extend this result
to arbitrary complex numbers `a`, showing that the circle average equals the positive part of the
logarithm, `circleAverage (log ‖· - a‖) 0 1 = = log⁺ ‖a‖`. This result, in turn, is a major
ingredient in the proof of Jensen's formula in complex analysis.
-/

open Filter Interval intervalIntegral MeasureTheory Real

variable {a : ℂ}

/-!
## Circle Integrability
-/

/--
If `a` is any complex number, the function `(log ‖· - a‖)` is circle integrable over every circle.
-/
lemma circleIntegrable_log_norm_sub_const {c : ℂ} (r : ℝ) :
    CircleIntegrable (log ‖· - a‖) c r :=
  circleIntegrable_log_norm_meromorphicOn (fun z hz ↦ by fun_prop)

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `‖a‖ = 1`.
-/

-- Integral computation used in `circleAverage_log_norm_id_sub_const₁`
private lemma circleAverage_log_norm_sub_const₁_integral :
    ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2 = 0 := by
  calc ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2
  _ = ∫ (x : ℝ) in 0..π, log (4 * sin x ^ 2) := by
    have {x : ℝ} : x / 2 = 2⁻¹ * x := by ring
    rw [intervalIntegral.integral_div, this, inv_mul_integral_comp_div
      (f := fun x ↦ log (4 * sin x ^ 2))]
    simp
  _ = ∫ (x : ℝ) in 0..π, log 4 + 2 * log (sin x) := by
    apply integral_congr_codiscreteWithin
    apply codiscreteWithin.mono (by tauto : Ι 0 π ⊆ Set.univ)
    have : AnalyticOnNhd ℝ (4 * sin · ^ 2) Set.univ := fun _ _ ↦ by fun_prop
    have := this.preimage_zero_mem_codiscrete (x := π / 2)
    simp only [sin_pi_div_two, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Set.preimage_compl, forall_const] at this
    filter_upwards [this] with a ha
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or] at ha
    rw [log_mul (by norm_num) (by simp_all), log_pow, Nat.cast_ofNat]
  _ = (∫ (x : ℝ) in 0..π, log 4) + 2 * ∫ (x : ℝ) in 0..π, log (sin x) := by
    rw [integral_add _root_.intervalIntegrable_const
      (by apply intervalIntegrable_log_sin.const_mul 2), intervalIntegral.integral_const_mul]
  _ = 0 := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_log_sin_zero_pi,
      (by norm_num : (4 : ℝ) = 2 * 2), log_mul two_ne_zero two_ne_zero]
    ring

/--
If `a : ℂ` has norm one, then the circle average `circleAverage (log ‖· - a‖) 0 1` vanishes.
-/
@[simp]
theorem circleAverage_log_norm_sub_const₁ (h : ‖a‖ = 1) :
    circleAverage (log ‖· - a‖) 0 1 = 0 := by
  -- Observing that the problem is rotation invariant, we rotate by an angle of `ζ = - arg a` and
  -- reduce the problem to the case where `a = 1`. The integral can then be evaluated by a direct
  -- computation.
  simp only [circleAverage, mul_inv_rev, smul_eq_mul, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
    or_false]
  right
  obtain ⟨ζ, hζ⟩ : ∃ ζ, a⁻¹ = circleMap 0 1 ζ := by simp [Set.exists_range_iff.1, h]
  calc ∫ x in 0..(2 * π), log ‖circleMap 0 1 x - a‖
  _ = ∫ x in 0..(2 * π), log ‖(circleMap 0 1 ζ) * (circleMap 0 1 x - a)‖ := by
    simp
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 (ζ + x) - (circleMap 0 1 ζ) * a‖ := by
    simp [mul_sub, circleMap, add_mul, Complex.exp_add]
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 (ζ + x) - 1‖ := by
    simp [← hζ, inv_mul_cancel₀ (by aesop : a ≠ 0)]
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 x - 1‖ := by
    have : Function.Periodic (log ‖circleMap 0 1 · - 1‖) (2 * π) :=
      fun x ↦ by simp [periodic_circleMap 0 1 x]
    have := this.intervalIntegral_add_eq (t := 0) (s := ζ)
    simp_all [integral_comp_add_left (log ‖circleMap 0 1 · - 1‖)]
  _ = ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2 := by
    apply integral_congr
    intro x hx
    simp only []
    rw [Complex.norm_def, log_sqrt (circleMap 0 1 x - 1).normSq_nonneg]
    congr
    calc Complex.normSq (circleMap 0 1 x - 1)
    _ = (cos x - 1) * (cos x - 1) + sin x * sin x := by
      simp [circleMap, Complex.normSq_apply]
    _ = sin x ^ 2 + cos x ^ 2 + 1 - 2 * cos x := by
      ring
    _ = 2 - 2 * cos x := by
      rw [sin_sq_add_cos_sq]
      norm_num
    _ = 2 - 2 * cos (2 * (x / 2)) := by
      rw [← mul_div_assoc]
      norm_num
    _ = 4 - 4 * cos (x / 2) ^ 2 := by
      rw [cos_two_mul]
      ring
    _ = 4 * sin (x / 2) ^ 2 := by
      nth_rw 1 [← mul_one 4, ← sin_sq_add_cos_sq (x / 2)]
      ring
  _ = 0 := circleAverage_log_norm_sub_const₁_integral
