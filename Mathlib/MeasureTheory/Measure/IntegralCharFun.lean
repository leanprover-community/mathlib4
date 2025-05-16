/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Integrals of characteristic functions

This file contains results about integrals of characteristic functions of measures, and lemmas
relating the measure of some sets to integrals of characteristic functions.

## Main statements

* `integral_charFun_Icc`: `∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ`
* TODO

-/

open RealInnerProductSpace Real Complex

namespace MeasureTheory

section Real

variable {μ : Measure ℝ} {r : ℝ}

lemma intervalIntegral_integral_swap {α E : Type*} {_ : MeasurableSpace α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [SFinite μ] {a b : ℝ} {f : ℝ → α → E}
    (h_int : Integrable (Function.uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ)) :
    ∫ x in a..b, ∫ y, f x y ∂μ = ∫ y, (∫ x in a..b, f x y) ∂μ := by
  rcases le_total a b with (hab | hab)
  · simp_rw [intervalIntegral.integral_of_le hab]
    simp only [hab, Set.uIoc_of_le] at h_int
    exact integral_integral_swap h_int
  · simp_rw [intervalIntegral.integral_of_ge hab]
    simp only [hab, Set.uIoc_of_ge] at h_int
    rw [integral_integral_swap h_int, integral_neg]

lemma integral_charFun_Icc [IsFiniteMeasure μ] (hr : 0 < r) :
    ∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ := by
  have h_int : Integrable (Function.uncurry fun (x y : ℝ) ↦ cexp (x * y * I))
      ((volume.restrict (Set.uIoc (-r) r)).prod μ) := by
    simp only [neg_le_self_iff, hr.le, Set.uIoc_of_le]
    -- integrable since bounded and the measure is finite
    rw [← integrable_norm_iff]
    swap; · exact Measurable.aestronglyMeasurable <| by fun_prop
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
    ring_nf
  _ = 2 * r * ∫ x, sinc (r * x) ∂μ := by
    norm_cast
    rw [integral_complex_ofReal, ← integral_const_mul]

lemma integrable_sinc_const_mul [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun x ↦ sinc (r * x)) μ :=
  (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable (by fun_prop)).mp
    integrable_sinc

lemma measureReal_abs_gt_le_integral_charFun [IsProbabilityMeasure μ] (hr : 0 < r) :
    μ.real {x | r < |x|}
      ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
  calc μ.real {x | r < |x|}
  _ = μ.real {x | 2 < |2 * r⁻¹ * x|} := by
    congr with x
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
        simp only [hx0, Set.mem_setOf_eq, mul_zero, abs_zero] at hx
        linarith
      rw [sinc_of_ne_zero hx_ne, le_sub_iff_add_le, ← le_sub_iff_add_le']
      norm_num
      rw [one_div]
      refine (sin_div_le_inv_abs _).trans ?_
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

lemma measureReal_abs_inner_gt_le_integral_charFun {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {mE : MeasurableSpace E} [OpensMeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {a : E} {r : ℝ} (hr : 0 < r) :
    μ.real {x | r < |⟪a, x⟫|}
      ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun μ (t • a)‖ := by
  have : IsProbabilityMeasure (μ.map (fun x ↦ ⟪a, x⟫)) := isProbabilityMeasure_map (by fun_prop)
  rw [Measure.real_def]
  convert measureReal_abs_gt_le_integral_charFun (μ := μ.map (fun x ↦ ⟪a, x⟫)) hr with x
  · rw [Measure.real_def, Measure.map_apply]
    · simp
    · fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · simp_rw [charFun_apply, inner_smul_right]
    simp only [conj_trivial, ofReal_mul, RCLike.inner_apply]
    rw [integral_map]
    · simp_rw [real_inner_comm a]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop

end MeasureTheory
