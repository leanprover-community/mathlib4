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
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: orthogonality

Chebyshev T polynomials are orthogonal with respect to `√(1 - x ^ 2)⁻¹`.

## Main statements

* integrable_measureT: continuous functions are integrable with respect to Lebesgue measure
  scaled by `√(1 - x ^ 2)⁻¹` and restricted to `(-1, 1]`.
* integral_eval_T_real_mul_evalT_real_measureT_of_ne:
  if `n ≠ m` then the integral of `T_n * T_m` equals `0`.
* integral_eval_T_real_mul_self_measureT_zero:
  if `n = m = 0` then the integral equals `π`.
* integral_eval_T_real_mul_self_measureT_of_ne_zero:
  if `n = m ≠ 0` then the integral equals `π / 2`.

## TODO

* Prove that Chebyshev U polynomials are orthogonal with respect to `√(1 - x ^ 2)`
* Bundle Chebyshev T polynomials into a HilbertBasis for MeasureTheory.Lp ℝ 2 measureT

-/
public section

namespace Polynomial.Chebyshev

open Real intervalIntegral MeasureTheory

/-- Lebesgue measure scaled by √(1 - x ^ 2)⁻¹. -/
noncomputable def measureT : Measure ℝ :=
  (volume.withDensity
    fun x ↦ ENNReal.ofNNReal ⟨√(1 - x ^ 2)⁻¹, by positivity⟩).restrict (Set.Ioc (-1) 1)

theorem integral_measureT (f : ℝ → ℝ) :
    ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := by
  rw [integral_of_le (by norm_num), measureT,
    restrict_withDensity (by measurability),
    integral_withDensity_eq_integral_smul (by measurability)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]

theorem intervalIntegrable_sqrt_one_sub_sq_inv :
    IntervalIntegrable (fun x ↦ √(1 - x ^ 2)⁻¹) volume (-1) 1 := by
  rw [intervalIntegrable_iff]
  refine integrableOn_deriv_of_nonneg continuous_arccos.neg.continuousOn (fun x hx ↦ ?_) (by simp)
  simpa using (hasDerivAt_arccos (by aesop) (by aesop)).neg

theorem integrable_measureT {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    Integrable f measureT := by
  replace hf : ContinuousOn f (Set.uIcc (-1) 1) := by rwa [Set.uIcc_of_lt (by norm_num)]
  have := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul hf
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)] at this
  rw [measureT, restrict_withDensity (by measurability),
    integrable_withDensity_iff (by measurability) (by simp)]
  unfold IntegrableOn at this
  convert this

open Set in
theorem integral_measureT_eq_integral_cos {f : ℝ → ℝ}
    (hf₁ : ContinuousOn (fun θ ↦ f (cos θ)) (Ioo 0 π))
    (hf₂ : IntegrableOn (fun x ↦ f (cos x)) (Icc 0 π))
    (hf₃ : IntegrableOn (fun x ↦ f x * √(1 - x ^ 2)⁻¹) (Icc (-1) 1)) :
    ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos θ) := calc
  ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := integral_measureT f
  _ = ∫ x in 1..-1, f x * -(√(1 - x ^ 2)⁻¹) := by
    rw [integral_symm, ← intervalIntegral.integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), f (cos θ) := by
    rw [← integral_comp_mul_deriv''' (f' := fun x => -(1 / √ (1 - x ^ 2))) (by fun_prop)
      (fun x hx ↦ (hasDerivAt_arccos (by aesop) (by aesop)).hasDerivWithinAt)]
    · simp_rw [Function.comp_apply]
      exact integral_congr <| fun x hx => by simp [cos_arccos (x := x) (by aesop) (by aesop)]
    · simpa using hf₁.mono <| by simpa using Real.strictAntiOn_arccos.image_Ioo_subset
    · simpa
    · refine IntegrableOn.congr_fun
        (by simpa only [neg_le_self_iff, zero_le_one, uIcc_of_ge] using hf₃.neg)
        (fun x hx ↦ ?_) (by simp)
      simp only [sqrt_inv, Pi.neg_apply, Function.comp_apply, one_div, mul_neg,
        cos_arccos (x := x) (by aesop) (by aesop)]
  _ = ∫ θ in 0..π, f (cos θ) := by simp

-- we provide this version for convenience.
open Set in
theorem integral_measureT_eq_integral_cos_of_continuous {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) :
    ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos θ) := by
  have : ContinuousOn (fun θ ↦ f (cos θ)) (Icc 0 π) := by
    refine hf.comp_continuous (by fun_prop) ?_ |>.continuousOn
    simpa [← abs_le] using abs_cos_le_one
  refine integral_measureT_eq_integral_cos (this.mono Ioo_subset_Icc_self) this.integrableOn_Icc ?_
  simpa using Iff.mp intervalIntegrable_iff' <|
    intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul <| by simpa

theorem integral_eval_T_real_measureT_zero :
    ∫ x, (T ℝ 0).eval x ∂measureT = π := by
  rw [integral_measureT_eq_integral_cos_of_continuous (by fun_prop)]; simp

theorem integral_eval_T_real_measureT_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x ∂measureT = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rw [integral_measureT_eq_integral_cos_of_continuous (by fun_prop)]
    simp_rw [T_real_cos]
    rwa [integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn), smul_eq_zero_iff_right (by aesop),
      mul_zero]
  trans ∫ θ in 0..n * π, (deriv sin) θ
  · refine integral_congr <| fun x hx => (congrFun deriv_sin x).symm
  by_cases! 0 ≤ n
  case pos => rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn (by positivity)]; simp
  case neg hn =>
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp
    exact mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr <| le_of_lt hn) pi_nonneg

theorem integral_eval_T_real_mul_eval_T_real_measureT (n m : ℤ) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT =
    ((∫ x, (T ℝ (n + m)).eval x ∂measureT) +
     (∫ x, (T ℝ (n - m)).eval x ∂measureT)) / 2 := by
  suffices ∫ x, (2 * T ℝ n * T ℝ m).eval x ∂measureT =
      (∫ x, (T ℝ (n + m)).eval x ∂measureT) +
      (∫ x, (T ℝ (n - m)).eval x ∂measureT) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [MeasureTheory.integral_const_mul] at this
    grind
  simp_rw [T_mul_T, eval_add]
  rw [MeasureTheory.integral_add
    (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop))]

theorem integral_eval_T_real_mul_eval_T_real_measureT_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT = 0 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind),
    integral_eval_T_real_measureT_of_ne_zero (by grind)]
  simp

theorem integral_eval_T_real_mul_self_measureT_zero :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂measureT = π := by
  simp_rw [← eval_mul, show (T ℝ 0) * (T ℝ 0) = T ℝ 0 by simp]
  exact integral_eval_T_real_measureT_zero

theorem integral_T_real_mul_self_measureT_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂measureT = π / 2 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind), sub_self,
    integral_eval_T_real_measureT_zero, zero_add]

end Polynomial.Chebyshev
