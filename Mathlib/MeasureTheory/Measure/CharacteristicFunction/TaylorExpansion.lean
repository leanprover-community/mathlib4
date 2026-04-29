/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Probability.Notation

/-!
# Taylor expansion of the characteristic function

This file provides the Taylor expansion of the characteristic function of a measure at `0`.

## Main statements

* `taylorWithinEval_charFun_zero`: If a finite measure `μ` over `ℝ` admits a moment of order `n`,
  then the Taylor expansion of its characteristic function at `0` at order `n` is given by
  `t ↦ ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ`.

## Tags

characteristic function, Taylor expansion
-/

public section


open ProbabilityTheory Complex Set VectorFourier
open scoped Nat RealInnerProductSpace Topology

namespace MeasureTheory

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ]

/-- The characteristic function of a finite measure with a moment of order `n` is `C^n`.
See `contDiff_charFun'` for the version proving `C^∞` by assuming all moments exist. -/
@[fun_prop]
theorem contDiff_charFun {n : ℕ} (hint : MemLp id n μ) :
    ContDiff ℝ n (charFun μ) := by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL ℝ) fun k hk ↦ ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))

/-- The characteristic function of a measure with all moments is `C^∞`. See `contDiff_charFun`
for the version proving only `C^n` by only assuming that the moment of order `n` exists. -/
@[fun_prop]
theorem contDiff_charFun' {n : ℕ∞} (hint : ∀ (k : ℕ), MemLp id k μ) :
    ContDiff ℝ n (charFun μ) := by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL ℝ) fun k hk ↦ ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' ((hint k).mono_exponent (by simp_all))

@[fun_prop]
lemma continuous_charFun : Continuous (charFun μ) := by
  refine contDiff_zero.1 (contDiff_charFun ?_)
  simp only [CharP.cast_eq_zero, memLp_zero_iff_aestronglyMeasurable]
  fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem iteratedFDeriv_charFun {n : ℕ} {t : E} (hint : MemLp id n μ) (x : Fin n → E) :
    iteratedFDeriv ℝ n (charFun μ) t x = I ^ n * ∫ y, (∏ i, ⟪y, x i⟫) * exp (⟪y, t⟫ * I) ∂μ := by
  have h : innerₗ E = (innerSL ℝ).toLinearMap₁₂ := rfl
  have hint' (k : ℕ) (hk : k ≤ (n : ℕ∞)) : Integrable (fun x ↦ ‖x‖ ^ k * ‖(1 : E → ℂ) x‖) μ := by
    simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
    refine MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))
  simp_rw [funext charFun_eq_fourierIntegral']
  rw [iteratedFDeriv_comp_const_smul]
  swap
  · rw [h]
    exact contDiff_fourierIntegral _ hint'
  simp only [mul_inv_rev, neg_smul]
  rw [h, iteratedFDeriv_fourierIntegral _ hint' (by fun_prop) le_rfl]
  simp only [ContinuousMultilinearMap.smul_apply, real_smul, ofReal_pow, ofReal_neg, ofReal_mul,
    ofReal_inv, ofReal_ofNat, ofReal_prod]
  rw [fourierIntegral_continuousMultilinearMap_apply Real.continuous_fourierChar]
  swap;
  · exact integrable_fourierPowSMulRight _ (by simpa using hint.integrable_norm_pow') (by fun_prop)
  simp only [fourierIntegral, Real.fourierChar, Circle.exp, ContinuousMap.coe_mk, ofReal_mul,
    ofReal_ofNat, innerSL, map_neg, map_smul, ContinuousLinearMap.toLinearMap₁₂_apply,
    LinearMap.mkContinuous₂_apply, innerₛₗ_apply_apply, smul_eq_mul, neg_neg, AddChar.coe_mk,
    ofReal_inv, fourierPowSMulRight_apply, Pi.ofNat_apply, real_smul, ofReal_prod, mul_one,
    Circle.smul_def]
  simp_rw [mul_left_comm (exp _), integral_const_mul, ← mul_assoc, ← mul_pow]
  field_simp
  congr with
  ring

end InnerProductSpace

section Real

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

set_option backward.isDefEq.respectTransparency false in
theorem iteratedDeriv_charFun {n : ℕ} {t : ℝ} (hint : MemLp id n μ) :
    iteratedDeriv n (charFun μ) t = I ^ n * ∫ x, x ^ n * exp (t * x * I) ∂μ := by
  rw [iteratedDeriv, iteratedFDeriv_charFun hint]
  simp

theorem iteratedDeriv_charFun_zero {n : ℕ} (hint : MemLp id n μ) :
    iteratedDeriv n (charFun μ) 0 = I ^ n * ∫ x, x ^ n ∂μ := by
  simp [iteratedDeriv_charFun hint]
  norm_cast

set_option backward.isDefEq.respectTransparency false in
lemma taylorWithinEval_charFun_zero {n : ℕ} (hint : MemLp id n μ) (t : ℝ) :
    taylorWithinEval (charFun μ) n univ 0 t
      = ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ := by
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun k hkn ↦ ?_
  push_cast
  have hint' : MemLp id k μ := hint.mono_exponent (by simp_all)
  simp [iteratedDeriv_charFun_zero hint', mul_pow, mul_comm, mul_assoc, mul_left_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

lemma taylorWithinEval_charFun_two_zero (hX : AEMeasurable X P)
    (hint : MemLp id 2 (P.map X)) (t : ℝ) :
    taylorWithinEval (charFun (P.map X)) 2 univ 0 t =
      1 + (P[X] : ℝ) * t * I - (P[X ^ 2] : ℝ) * t ^ 2 / 2 := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  convert taylorWithinEval_charFun_zero hint t with x
  simp only [Pi.pow_apply, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one,
    integral_const, probReal_univ, smul_eq_mul, ofReal_one, Nat.factorial_one, pow_one, one_mul,
    Nat.factorial_two, Nat.cast_ofNat]
  rw [integral_map, integral_map]
  any_goals fun_prop
  simp [field]
  ring

lemma taylorWithinEval_charFun_two_zero' (hX : AEMeasurable X P)
    (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : ℝ) :
    taylorWithinEval (charFun (P.map X)) 2 univ 0 t = 1 - t ^ 2 / 2 := by
  rw [taylorWithinEval_charFun_two_zero hX, h0, h1]
  · simp
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp [← Pi.pow_apply, h1]

lemma taylor_charFun_two (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) :
    (fun t ↦ charFun (P.map X) t - (1 - t ^ 2 / 2)) =o[𝓝 0] fun t ↦ t ^ 2 := by
  simp_rw [← taylorWithinEval_charFun_two_zero' (by fun_prop) h0 h1]
  convert taylor_isLittleO_univ ?_
  · simp
  refine contDiff_charFun <|
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp_all

end Real

end MeasureTheory
