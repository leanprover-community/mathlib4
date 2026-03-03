/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Notation

/-!
# Taylor expansion of the characteristic function

This file provides the Taylor expansion of the characteristic function of a measure.
-/

open MeasureTheory ProbabilityTheory Complex Set
open scoped Nat Real NNReal ENNReal Topology RealInnerProductSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ]

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
theorem contDiff_charFun {n : ℕ} (hint : Integrable (‖·‖ ^ n) μ) :
    ContDiff ℝ n (charFun μ) := by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (VectorFourier.contDiff_fourierIntegral (L := innerSL ℝ) fun k hk ↦ ?_).comp (by fun_prop)
  simpa using integrable_norm_pow_of_le aestronglyMeasurable_id (Nat.cast_le.1 hk) hint

@[fun_prop]
lemma continuous_charFun : Continuous (charFun μ) :=
  contDiff_zero.1 (contDiff_charFun (by simp))

set_option backward.isDefEq.respectTransparency false in
open VectorFourier in
theorem iteratedFDeriv_charFun {n : ℕ} {t : E} (hint : Integrable (‖·‖ ^ n) μ) (x : Fin n → E) :
    iteratedFDeriv ℝ n (charFun μ) t x = I ^ n * ∫ y, (∏ i, ⟪y, x i⟫) * exp (⟪y, t⟫ * I) ∂μ := by
  have h : innerₗ E = (innerSL ℝ).toLinearMap₁₂ := rfl
  have hint' (k : ℕ) (hk : k ≤ (n : ℕ∞)) : Integrable (fun x ↦ ‖x‖ ^ k * ‖(1 : E → ℂ) x‖) μ := by
    simpa using integrable_norm_pow_of_le aestronglyMeasurable_id (Nat.cast_le.1 hk) hint
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
  swap; · exact integrable_fourierPowSMulRight _ (by simpa) (by fun_prop)
  simp only [fourierIntegral, Real.fourierChar, Circle.exp, ContinuousMap.coe_mk, ofReal_mul,
    ofReal_ofNat, innerSL, map_neg, map_smul, ContinuousLinearMap.toLinearMap₁₂_apply,
    LinearMap.mkContinuous₂_apply, innerₛₗ_apply_apply, smul_eq_mul, neg_neg, AddChar.coe_mk,
    ofReal_inv, fourierPowSMulRight_apply, Pi.ofNat_apply, real_smul, ofReal_prod, mul_one,
    Circle.smul_def]
  simp_rw [mul_left_comm (exp _), integral_const_mul, ← mul_assoc, ← mul_pow]
  field_simp
  congr with
  ring_nf

end InnerProductSpace

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

set_option backward.isDefEq.respectTransparency false in
theorem iteratedDeriv_charFun {n : ℕ} {t : ℝ} (hint : Integrable (|·| ^ n) μ) :
    iteratedDeriv n (charFun μ) t = I ^ n * ∫ x, x ^ n * exp (t * x * I) ∂μ := by
  rw [iteratedDeriv, iteratedFDeriv_charFun]
  swap; · exact hint
  simp

set_option backward.isDefEq.respectTransparency false in
theorem iteratedDeriv_charFun_zero {n : ℕ} (hint : Integrable (|·| ^ n) μ) :
    iteratedDeriv n (charFun μ) 0 = I ^ n * ∫ x, x ^ n ∂μ := by
  simp [iteratedDeriv_charFun hint]
  norm_cast

set_option backward.isDefEq.respectTransparency false in
lemma taylorWithinEval_charFun_zero {n : ℕ} (hint : Integrable (|·| ^ n) μ) (t : ℝ) :
    taylorWithinEval (charFun μ) n univ 0 t
      = ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ := by
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun k hkn ↦ ?_
  push_cast
  have hint' : Integrable (fun x ↦ |x| ^ k) μ :=
    integrable_norm_pow_of_le aestronglyMeasurable_id (Finset.mem_range_succ_iff.1 hkn) hint
  simp [iteratedDeriv_charFun_zero hint', mul_pow, mul_comm, mul_assoc, mul_left_comm]

theorem taylor_charFun {n : ℕ} (hint : Integrable (|·| ^ n) μ) :
    (fun t ↦ charFun μ t -
      ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ) =o[𝓝 0]
    fun t ↦ t ^ n := by
  convert taylor_isLittleO_univ (contDiff_charFun hint)
  · exact (taylorWithinEval_charFun_zero hint _).symm
  · simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

set_option backward.isDefEq.respectTransparency false in
lemma taylor_charFun_two' (hX : Measurable X) (hint : Integrable (|·| ^ 2) (P.map X)) :
    (fun t ↦ charFun (P.map X) t - (1 + P[X] * t * I - P[X ^ 2] * t ^ 2 / 2))
      =o[𝓝 0] fun t ↦ t ^ 2 := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  convert taylor_charFun hint with x
  simp only [Pi.pow_apply, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one,
    integral_const, probReal_univ, smul_eq_mul, ofReal_one, Nat.factorial_one, pow_one, one_mul,
    Nat.factorial_two, Nat.cast_ofNat]
  rw [integral_map, integral_map, ← integral_complex_ofReal, ← integral_complex_ofReal]
  any_goals fun_prop
  simp [field]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma taylor_charFun_two {X : Ω → ℝ} (hX : Measurable X) {P : Measure Ω} [IsProbabilityMeasure P]
    (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) :
    (fun t ↦ charFun (P.map X) t - (1 - t ^ 2 / 2)) =o[𝓝 0] fun t ↦ t ^ 2 := by
  convert taylor_charFun_two' hX ?_
  · simp [h0, integral_complex_ofReal]
  · simp [h1, ← Pi.pow_apply, integral_complex_ofReal]
  · infer_instance
  · apply Integrable.of_integral_ne_zero
    rw [integral_map]
    any_goals fun_prop
    simp_rw [sq_abs, ← Pi.pow_apply, h1]
    grind
