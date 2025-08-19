/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Integrals of characteristic functions

This file contains results about integrals of characteristic functions, and lemmas
relating the measure of some sets to integrals of characteristic functions.

## Main statements

* `integral_charFun_Icc`: `∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ`
* `measureReal_abs_gt_le_integral_charFun`: bound on the measure of the set
  `{x | r < |x|}` in terms of the integral of the characteristic function of `μ`, for `μ` a
  probability measure on `ℝ`:
  `μ.real {x | r < |x|} ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖`
* `measureReal_abs_dual_gt_le_integral_charFunDual`: an application of the previous lemma in a
  normed space `E`, which gives for all `L : Dual ℝ E`,
  `μ.real {x | r < |L x|} ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFunDual μ (t • L)‖`
* `measureReal_abs_inner_gt_le_integral_charFun`: an application in an inner product space,
  which gives for all `a`,
  `μ.real {x | r < |⟪a, x⟫|} ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun μ (t • a)‖`

-/

open RealInnerProductSpace Real Complex NormedSpace

namespace MeasureTheory

section Real

variable {μ : Measure ℝ} {r : ℝ}

lemma integral_charFun_Icc [IsFiniteMeasure μ] (hr : 0 < r) :
    ∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ := by
  have h_int : Integrable (Function.uncurry fun (x y : ℝ) ↦ cexp (x * y * I))
      ((volume.restrict (Set.uIoc (-r) r)).prod μ) := by
    simp only [neg_le_self_iff, hr.le, Set.uIoc_of_le]
    -- integrable since the function has norm 1 everywhere and the measure is finite
    rw [← integrable_norm_iff (by fun_prop)]
    suffices (fun a => ‖Function.uncurry (fun (x y : ℝ) ↦ cexp (x * y * I)) a‖) = fun _ ↦ 1 by
      rw [this]
      fun_prop
    ext p
    rw [← Prod.mk.eta (p := p)]
    norm_cast
    simp only [Function.uncurry_apply_pair, norm_exp_ofReal_mul_I]
  calc ∫ t in -r..r, charFun μ t
  _ = ∫ x in -r..r, ∫ y, cexp (x * y * I) ∂μ := by simp_rw [charFun_apply_real]
  _ = ∫ y, ∫ x in -r..r, cexp (x * y * I) ∂volume ∂μ := by
    rw [intervalIntegral_integral_swap h_int]
  _ = ∫ y, if r * y = 0 then 2 * (r : ℂ)
      else y⁻¹ * ∫ x in -(y * r)..y * r, cexp (x * I) ∂volume ∂μ := by
    congr with y
    by_cases hy : y = 0
    · simp [hy, two_mul]
    simp only [mul_eq_zero, hr.ne', hy, or_self, ↓reduceIte, ofReal_inv]
    have h := intervalIntegral.integral_comp_smul_deriv (E := ℂ) (a := -r) (b := r)
      (f := fun x ↦ y * x) (f' := fun _ ↦ y) (g := fun x ↦ cexp (x * I)) ?_ (by fun_prop)
      (by fun_prop)
    swap
    · intro x hx
      simp_rw [mul_comm y]
      exact hasDerivAt_mul_const _
    simp only [Function.comp_apply, ofReal_mul, real_smul, intervalIntegral.integral_const_mul,
      mul_neg] at h
    rw [← h, ← mul_assoc]
    norm_cast
    simp [mul_comm _ y, mul_inv_cancel₀ hy]
  _ = ∫ x, 2 * (r : ℂ) * sinc (r * x) ∂μ := by
    congr with y
    rw [integral_exp_mul_I_eq_sinc]
    split_ifs with hry
    · simp [hry]
    have hy : y ≠ 0 := fun hy ↦ hry (by simp [hy])
    norm_cast
    field_simp
  _ = 2 * r * ∫ x, sinc (r * x) ∂μ := by
    norm_cast
    rw [integral_complex_ofReal, ← integral_const_mul]

/-- A bound on the measure of the set `{x | r < |x|}` in terms of the integral of
the characteristic function, for a probability measure on `ℝ`. -/
lemma measureReal_abs_gt_le_integral_charFun [IsProbabilityMeasure μ] (hr : 0 < r) :
    μ.real {x | r < |x|} ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
  have integrable_sinc_const_mul (r : ℝ) : Integrable (fun x ↦ sinc (r * x)) μ :=
    (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable (by fun_prop)).mp
      integrable_sinc
  calc μ.real {x | r < |x|}
  _ = μ.real {x | 2 < |2 * r⁻¹ * x|} := by
    congr 1 with x
    simp only [Set.mem_setOf_eq, abs_mul, Nat.abs_ofNat]
    rw [abs_of_nonneg (a := r⁻¹) (by positivity), mul_assoc, ← inv_mul_lt_iff₀ (by positivity),
      inv_mul_cancel₀ (by positivity), lt_inv_mul_iff₀ (by positivity), mul_one]
  _ = ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 ∂μ := by simp
  _ = 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 2⁻¹ ∂μ := by
    rw [← integral_const_mul]
    congr with _
    rw [mul_inv_cancel₀ (by positivity)]
  _ ≤ 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    gcongr (2 : ℝ) * ?_
    refine setIntegral_mono_on ?_
      ((integrable_const _).sub (integrable_sinc_const_mul _)).integrableOn ?_ fun x hx ↦ ?_
    · exact Integrable.integrableOn <| by fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    · have hx_ne : 2 * r⁻¹ * x ≠ 0 := by
        intro hx0
        simp only [hx0, Set.mem_setOf_eq, abs_zero] at hx
        linarith
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
      norm_num
      rw [one_div]
      refine (sinc_le_inv_abs hx_ne).trans ?_
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (le_of_lt hx)
  _ ≤ 2 * ∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    gcongr
    refine setIntegral_le_integral ((integrable_const _).sub (integrable_sinc_const_mul _))
      <| ae_of_all _ fun x ↦ ?_
    simp only [Pi.zero_apply, sub_nonneg]
    exact sinc_le_one (2 * r⁻¹ * x)
  _ ≤ 2 * ‖∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ‖ := by
    gcongr
    exact Real.le_norm_self _
  _ = 2⁻¹ * r *
      ‖2 * (r : ℂ)⁻¹ + 2 * r⁻¹ - 2 * (2 * r⁻¹) * ∫ x, sinc (2 * r⁻¹ * x) ∂μ‖ := by
    norm_cast
    rw [← two_mul, mul_assoc 2, ← mul_sub, norm_mul, Real.norm_ofNat, ← mul_assoc,
      ← mul_one_sub, norm_mul, Real.norm_of_nonneg (r := 2 * r⁻¹) (by positivity), ← mul_assoc]
    congr
    · ring_nf
      rw [mul_inv_cancel₀ (by positivity), one_mul]
    · rw [integral_sub (integrable_const _) (integrable_sinc_const_mul _)]
      simp
  _ = 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_charFun, neg_mul,
      integral_charFun_Icc (by positivity)]
    simp

end Real

/-- For a probability measure on a normed space `E` and `L : Dual ℝ E`, a bound on the measure
of the set `{x | r < |L x|}` in terms of the integral of the characteristic function. -/
lemma measureReal_abs_dual_gt_le_integral_charFunDual {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {mE : MeasurableSpace E} [OpensMeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] (L : StrongDual ℝ E) {r : ℝ} (hr : 0 < r) :
    μ.real {x | r < |L x|} ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFunDual μ (t • L)‖ := by
  have : IsProbabilityMeasure (μ.map L) := isProbabilityMeasure_map (by fun_prop)
  convert measureReal_abs_gt_le_integral_charFun (μ := μ.map L) hr with x
  · rw [map_measureReal_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · rw [charFun_map_eq_charFunDual_smul]

/-- A bound on the measure of the set `{x | r < |⟪a, x⟫|}` in terms of the integral of
the characteristic function, for a probability measure on an inner product space. -/
lemma measureReal_abs_inner_gt_le_integral_charFun {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {mE : MeasurableSpace E} [OpensMeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {a : E} {r : ℝ} (hr : 0 < r) :
    μ.real {x | r < |⟪a, x⟫|} ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun μ (t • a)‖ := by
  have : IsProbabilityMeasure (μ.map (fun x ↦ ⟪a, x⟫)) := isProbabilityMeasure_map (by fun_prop)
  convert measureReal_abs_gt_le_integral_charFun (μ := μ.map (fun x ↦ ⟪a, x⟫)) hr with x
  · rw [map_measureReal_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · simp only [charFun_apply, inner_smul_right, conj_trivial, ofReal_mul, RCLike.inner_apply]
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [real_inner_comm a]

end MeasureTheory
