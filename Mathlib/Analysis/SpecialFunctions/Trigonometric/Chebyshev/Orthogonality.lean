/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Chebyshev polynomials over the reals: orthogonality

Chebyshev T polynomials are orthogonal with respect to `1 / √ (1 - x ^ 2)`.

## Main statements

* integrable_T_real_mul_T: `T_n (x) * T_m (x) * (1 / √ (1 - x ^ 2))` is integrable.
* integral_T_real_mul_T_real_of_ne: if `n ≠ m` then the integral equals `0`.
* integral_T_real_mul_self_zero: if `n = m = 0` then the integral equals `π`.
* integral_T_real_mul_self_of_ne_zero: if `n = m ≠ 0` then the integral equals `π / 2`.

-/
@[expose] public section

namespace Polynomial.Chebyshev

open Real intervalIntegral

theorem integrable_T_real (n : ℤ) :
    IntervalIntegrable (fun x => (T ℝ n).eval x * (1 / √(1 - x ^ 2)))
    MeasureTheory.volume (-1) 1 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)]
  refine ⟨?_, ?_⟩
  · suffices MeasureTheory.AEStronglyMeasurable
      (fun x ↦ (T ℝ n).eval (cos (arccos x)) * (1 / √(1 - x ^ 2)))
      (MeasureTheory.volume.restrict (Set.Ioc (-1) 1)) by
      apply MeasureTheory.AEStronglyMeasurable.congr this
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
      dsimp; congr 2
      rw [cos_arccos (by grind) (by grind)]
    measurability
  · apply MeasureTheory.HasFiniteIntegral.mono (g := fun x => (1 / √(1 - x ^ 2)))
    · suffices MeasureTheory.IntegrableOn (fun x ↦ (1 / √(1 - x ^ 2))) (Set.Ioc (-1) 1) from this.2
      refine integrableOn_deriv_of_nonneg (g := -arccos)
        continuous_arccos.neg.continuousOn (fun x hx => ?_) (by simp)
      · convert (@hasDerivAt_arccos x (by aesop) (by aesop)).neg using 1
        simp
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
      simp_rw [norm_mul, norm_eq_abs]
      calc
        |(T ℝ n).eval x| * |(1 / √(1 - x ^ 2))| ≤ 1 * |(1 / √(1 - x ^ 2))| := by
          gcongr; exact abs_eval_T_real_le_one n (by grind)
        _ = |(1 / √(1 - x ^ 2))| := by simp

theorem integral_T_real (n : ℤ) :
    ∫ x in -1..1, (T ℝ n).eval x * (1 / √(1 - x ^ 2)) = ∫ θ in 0..π, cos (n * θ) := calc
  ∫ x in -1..1, (T ℝ n).eval x * (1 / √(1 - x ^ 2)) =
    ∫ x in 1..-1, (T ℝ n).eval x * -(1 / √(1 - x ^ 2)) := by
    rw [integral_symm, ← integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), (T ℝ n).eval (cos θ) := by
    have h : arccos '' Set.uIcc 1 (-1) = Set.Icc 0 π := by
      refine Set.ext fun θ => ⟨fun hθ => ?_, fun hθ => ⟨cos θ, ⟨?_, ?_⟩⟩⟩
      · grind only [= Set.mem_image, = Set.mem_Icc, !arccos_nonneg, !arccos_le_pi]
      · simp [cos_le_one, neg_one_le_cos]
      · exact arccos_cos (Set.mem_Icc.mp hθ).1 (Set.mem_Icc.mp hθ).2
    rw [← integral_comp_mul_deriv''' (f' := fun x => -(1 / √ (1 - x ^ 2)))]
    · simp_rw [Function.comp_apply]
      exact integral_congr <| fun x hx => by rw [cos_arccos (by aesop) (by aesop)]
    · exact continuous_arccos.continuousOn
    · exact fun x hx => (hasDerivAt_arccos (x := x) (by aesop) (by aesop)).hasDerivWithinAt
    · apply Continuous.continuousOn; continuity
    · rw [h]
      refine MeasureTheory.IntegrableOn.of_bound (C := 1) (by simp) (by measurability) ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => ?_)
      simpa [T_real_cos] using abs_cos_le_one _
    · refine ⟨by measurability, ?_⟩
      apply MeasureTheory.HasFiniteIntegral.mono (g := fun x => (1 / √(1 - x ^ 2)))
      · suffices MeasureTheory.IntegrableOn (fun x ↦ (1 / √(1 - x ^ 2))) (Set.Icc (-1) 1) by
          rw [Set.uIcc_of_ge (by norm_num)]; exact this.2
        rw [integrableOn_Icc_iff_integrableOn_Ioc]
        refine integrableOn_deriv_of_nonneg (g := -arccos)
          continuous_arccos.neg.continuousOn (fun x hx => ?_) (by simp)
        convert (@hasDerivAt_arccos x (by aesop) (by aesop)).neg using 1
        simp
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => ?_)
        simp_rw [T_real_cos, norm_mul, norm_eq_abs]
        calc
          |cos (n * arccos x)| * |-(1 / √(1 - x ^ 2))| ≤ 1 * |-(1 / √(1 - x ^ 2))| := by
            gcongr; exact abs_cos_le_one _
          _ = |(1 / √(1 - x ^ 2))| := by simp
  _ = ∫ θ in 0..π, cos (n * θ) := by simp

theorem integral_T_real_zero :
    ∫ x in -1..1, (T ℝ 0).eval x * (1 / √(1 - x ^ 2)) = π := by
  rw [integral_T_real 0]; simp

theorem integral_T_real_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x in -1..1, (T ℝ n).eval x * (1 / √(1 - x ^ 2)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rwa [integral_T_real n, integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn),
      smul_eq_zero_iff_right (by aesop), mul_zero]
  trans ∫ θ in 0..n * π, (deriv sin) θ
  · refine integral_congr <| fun x hx => (congrFun deriv_sin x).symm
  by_cases! 0 ≤ n
  case pos => rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn (by positivity)]; simp
  case neg hn =>
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp
    exact mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr <| le_of_lt hn) pi_nonneg

theorem integrable_T_real_mul_T (n m : ℤ) :
    IntervalIntegrable (fun x => (T ℝ n).eval x * (T ℝ m).eval x * (1 / √(1 - x ^ 2)))
    MeasureTheory.volume (-1) 1 := by
  suffices IntervalIntegrable (fun x => (2 * T ℝ n * T ℝ m).eval x * (1 / √(1 - x ^ 2)))
      MeasureTheory.volume (-1) 1 by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    convert IntervalIntegrable.const_mul this (1 / 2) using 1
    grind
  simp_rw [T_mul_T, eval_add, add_mul]
  exact IntervalIntegrable.add (integrable_T_real _) (integrable_T_real _)

theorem integral_T_real_mul_T_real (n m : ℤ) :
    ∫ x in -1..1, (T ℝ n).eval x * (T ℝ m).eval x * (1 / √(1 - x ^ 2)) =
    ((∫ x in -1..1, (T ℝ (n + m)).eval x * (1 / √(1 - x ^ 2))) +
     (∫ x in -1..1, (T ℝ (n - m)).eval x * (1 / √(1 - x ^ 2)))) / 2 := by
  suffices ∫ x in -1..1, (2 * T ℝ n * T ℝ m).eval x * (1 / √(1 - x ^ 2)) =
      (∫ x in -1..1, (T ℝ (n + m)).eval x * (1 / √(1 - x ^ 2))) +
      (∫ x in -1..1, (T ℝ (n - m)).eval x * (1 / √(1 - x ^ 2))) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [integral_const_mul] at this
    grind
  simp_rw [T_mul_T, eval_add, add_mul]
  rw [integral_add (integrable_T_real _) (integrable_T_real _)]

theorem integral_T_real_mul_T_real_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x in -1..1, (T ℝ n).eval x * (T ℝ m).eval x * (1 / √(1 - x ^ 2)) = 0 := by
  rw [integral_T_real_mul_T_real, integral_T_real_of_ne_zero (by grind),
    integral_T_real_of_ne_zero (by grind)]
  simp

theorem integral_T_real_mul_self_zero :
    ∫ x in -1..1, (T ℝ 0).eval x * (T ℝ 0).eval x * (1 / √(1 - x ^ 2)) = π := by
  simp_rw [← eval_mul, show (T ℝ 0) * (T ℝ 0) = T ℝ 0 by simp]
  exact integral_T_real_zero

theorem integral_T_real_mul_self_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x in -1..1, (T ℝ n).eval x * (T ℝ n).eval x * (1 / √(1 - x ^ 2)) = π / 2 := by
  rw [integral_T_real_mul_T_real, integral_T_real_of_ne_zero (by grind), sub_self,
    integral_T_real_zero, zero_add]

end Polynomial.Chebyshev
