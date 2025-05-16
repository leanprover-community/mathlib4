/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel, Rémy Degenne, Thomas Zhu
-/
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Characteristic Function of a Finite Measure

This file defines the characteristic function of a finite measure on a topological vector space `V`.

The characteristic function of a finite measure `P` on `V` is the mapping
`W → ℂ, w => ∫ v, e (L v w) ∂P`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map.

A typical example is `V = W = ℝ` and `L v w = v * w`.

The integral is expressed as `∫ v, char he hL w v ∂P`, where `char he hL w` is the
bounded continuous function `fun v ↦ e (L v w)` and `he`, `hL` are continuity hypotheses on `e`
and `L`.

## Main definitions

* `innerProbChar`: the bounded continuous map `x ↦ exp(⟪x, t⟫ * I)` in an inner product space.
  This is `char` for the inner product bilinear map and the additive character `e = probChar`.
* `charFun μ t`: the characteristic function of a measure `μ` at `t` in an inner product space `E`.
  This is defined as `∫ x, exp (⟪x, t⟫ * I) ∂μ`, where `⟪x, t⟫` is the inner product on `E`.
  It is equal to `∫ v, innerProbChar w v ∂P` (see `charFun_eq_integral_innerProbChar`).
* `probCharDual`: the bounded continuous map `x ↦ exp (L x * I)`, for a continuous linear form `L`.
* `charFunDual μ L`: the characteristic function of a measure `μ` at `L : Dual ℝ E` in
  a normed space `E`. This is the integral `∫ v, exp (L v * I) ∂μ`.

## Main statements

* `ext_of_integral_char_eq`: Assume `e` and `L` are non-trivial. If the integrals of `char`
  with respect to two finite measures `P` and `P'` coincide, then `P = P'`.
* `Measure.ext_of_charFun`: If the characteristic functions `charFun` of two finite measures
  `μ` and `ν` on a complete second-countable inner product space coincide, then `μ = ν`.
* `Measure.ext_of_charFunDual`: If the characteristic functions `charFunDual` of two finite measures
  `μ` and `ν` on a Banach space coincide, then `μ = ν`.

-/

open BoundedContinuousFunction RealInnerProductSpace Real Complex ComplexConjugate NormedSpace

namespace BoundedContinuousFunction

variable {E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- The bounded continuous map `x ↦ exp(⟪x, t⟫ * I)`. -/
noncomputable
def innerProbChar (t : E) : E →ᵇ ℂ :=
  char continuous_probChar (L := bilinFormOfRealInner) continuous_inner t

lemma innerProbChar_apply (t x : E) : innerProbChar t x = exp (⟪x, t⟫ * I) := rfl

@[simp]
lemma innerProbChar_zero : innerProbChar (0 : E) = 1 := by simp [innerProbChar]

/-- The bounded continuous map `x ↦ exp (L x * I)`, for a continuous linear form `L`. -/
noncomputable
def probCharDual (L : Dual ℝ F) : F →ᵇ ℂ :=
  char continuous_probChar (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₂)
    isBoundedBilinearMap_apply.symm.continuous L

lemma probCharDual_apply (L : Dual ℝ F) (x : F) : probCharDual L x = exp (L x * I) := rfl

@[simp]
lemma probCharDual_zero : probCharDual (0 : Dual ℝ F) = 1 := by simp [probCharDual]

end BoundedContinuousFunction

namespace MeasureTheory

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle}

section ext

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [PseudoEMetricSpace V] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}

/-- If the integrals of `char` with respect to two finite measures `P` and `P'` coincide, then
`P = P'`. -/
theorem ext_of_integral_char_eq (he : Continuous e) (he' : e ≠ 1)
    (hL' : ∀ v ≠ 0, L v ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {P P' : Measure V} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ w, ∫ v, char he hL w v ∂P = ∫ v, char he hL w v ∂P') :
    P = P' := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (separatesPoints_charPoly he he' hL hL')
  intro _ hg
  simp only [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  rw [hw]
  have hsum (P : Measure V) [IsFiniteMeasure P] :
      ∫ v, ∑ a ∈ w.support, w a * e (L v a) ∂P = ∑ a ∈ w.support, ∫ v, w a * e (L v a) ∂P :=
    integral_finset_sum w.support
      fun a ha => Integrable.const_mul (integrable P (char he hL a)) _
  rw [hsum P, hsum P']
  apply Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul, MeasureTheory.integral_const_mul, mul_eq_mul_left_iff]
  exact Or.inl (h i)

end ext

section InnerProductSpace

variable {E : Type*} {mE : MeasurableSpace E} {μ : Measure E} {t : E}

/-- The characteristic function of a measure in an inner product space. -/
noncomputable def charFun [Inner ℝ E] (μ : Measure E) (t : E) : ℂ := ∫ x, exp (⟪x, t⟫ * I) ∂μ

lemma charFun_apply [Inner ℝ E] (t : E) : charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ := rfl

lemma charFun_apply_real {μ : Measure ℝ} (t : ℝ) :
    charFun μ t = ∫ x, exp (t * x * I) ∂μ := by simp [charFun_apply]

variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
lemma charFun_zero (μ : Measure E) : charFun μ 0 = μ.real Set.univ := by
  simp [charFun_apply]

@[simp]
lemma charFun_zero_measure : charFun (0 : Measure E) t = 0 := by simp [charFun_apply]

@[simp]
lemma charFun_neg (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun_apply, ← integral_conj, ← exp_conj]

/-- `charFun` as the integral of a bounded continuous function. -/
lemma charFun_eq_integral_innerProbChar : charFun μ t = ∫ v, innerProbChar t v ∂μ := by
  simp [charFun_apply, innerProbChar_apply]

lemma charFun_eq_integral_probChar (t : E) : charFun μ t = ∫ x, (probChar ⟪x, t⟫ : ℂ) ∂μ := by
  simp [charFun_apply, probChar_apply]

/-- `charFun` is a Fourier integral for the inner product and the character `probChar`. -/
lemma charFun_eq_fourierIntegral (t : E) :
    charFun μ t = VectorFourier.fourierIntegral probChar μ bilinFormOfRealInner 1 (-t) := by
  simp [charFun_apply, VectorFourier.fourierIntegral_probChar]

/-- `charFun` is a Fourier integral for the inner product and the character `fourierChar`. -/
lemma charFun_eq_fourierIntegral' (t : E) :
    charFun μ t
      = VectorFourier.fourierIntegral fourierChar μ bilinFormOfRealInner 1 (-(2 * π)⁻¹ • t) := by
  simp only [charFun_apply, VectorFourier.fourierIntegral, neg_smul,
    bilinFormOfRealInner_apply_apply, inner_neg_right, inner_smul_right, neg_neg,
    fourierChar_apply', Pi.ofNat_apply, Circle.smul_def, Circle.coe_exp, ofReal_mul, ofReal_ofNat,
    ofReal_inv, smul_eq_mul, mul_one]
  congr with x
  rw [← mul_assoc, mul_inv_cancel₀ (by simp [pi_ne_zero]), one_mul]

lemma norm_charFun_le (t : E) : ‖charFun μ t‖ ≤ μ.real Set.univ := by
  rw [charFun_eq_fourierIntegral]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq (by simp)

lemma norm_charFun_le_one [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ ≤ 1 :=
  (norm_charFun_le _).trans_eq (by simp)

lemma norm_one_sub_charFun_le_two [IsProbabilityMeasure μ] : ‖1 - charFun μ t‖ ≤ 2 :=
  calc ‖1 - charFun μ t‖
  _ ≤ ‖(1 : ℂ)‖ + ‖charFun μ t‖ := norm_sub_le _ _
  _ ≤ 1 + 1 := by simp [norm_charFun_le_one]
  _ = 2 := by norm_num

@[fun_prop, measurability]
lemma stronglyMeasurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    StronglyMeasurable (charFun μ) :=
  (Measurable.stronglyMeasurable (by fun_prop)).integral_prod_left

@[fun_prop, measurability]
lemma measurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    Measurable (charFun μ) :=
  stronglyMeasurable_charFun.measurable

lemma intervalIntegrable_charFun {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} :
    IntervalIntegrable (charFun μ) volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ ↦ μ.real Set.univ) (by simp)
    stronglyMeasurable_charFun.aestronglyMeasurable (ae_of_all _ norm_charFun_le)

lemma charFun_map_smul [BorelSpace E] [SecondCountableTopology E] (r : ℝ) (t : E) :
    charFun (μ.map (r • ·)) t = charFun μ (r • t) := by
  rw [charFun_apply, charFun_apply,
    integral_map (by fun_prop) (Measurable.aestronglyMeasurable <| by fun_prop)]
  simp_rw [inner_smul_right, ← real_inner_smul_left]

lemma charFun_map_mul {μ : Measure ℝ} (r t : ℝ) :
    charFun (μ.map (r * ·)) t = charFun μ (r * t) := charFun_map_smul r t

variable {E : Type*} [MeasurableSpace E] {μ ν : Measure E} {t : E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]

/-- If the characteristic functions `charFun` of two finite measures `μ` and `ν` on
a complete second-countable inner product space coincide, then `μ = ν`. -/
theorem Measure.ext_of_charFun [CompleteSpace E]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : charFun μ = charFun ν) :
    μ = ν := by
  simp_rw [funext_iff, charFun_eq_integral_innerProbChar] at h
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one (L := bilinFormOfRealInner)
    ?_ ?_ h
  · exact fun v hv ↦ DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact continuous_inner

section bounds

lemma integral_exp_Icc (r : ℝ) : ∫ t in -r..r, cexp (t * I) = 2 * Real.sin r :=
  calc ∫ t in -r..r, cexp (t * I)
  _ = (cexp (I * r) - cexp (I * (-r))) / I := by
    simp_rw [mul_comm _ I]
    rw [integral_exp_mul_complex]
    · simp
    · simp
  _ = 2 * Real.sin r := by
    simp only [mul_comm I, exp_mul_I, Complex.cos_neg, Complex.sin_neg, add_sub_add_left_eq_sub,
      div_I, ofReal_sin]
    rw [sub_mul, mul_assoc, mul_assoc, two_mul]
    simp

lemma integral_exp_Icc_eq_sinc (r : ℝ) :
    ∫ t in -r..r, cexp (t * I) = 2 * r * sinc r := by
  rw [integral_exp_Icc]
  by_cases hr : r = 0
  · simp [hr]
  rw [sinc_of_ne_zero hr]
  norm_cast
  field_simp
  ring

lemma integral_charFun_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    ∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ := by
  have h_int r : Integrable (Function.uncurry fun (x y : ℝ) ↦ cexp (x * y * I))
      ((volume.restrict (Set.Ioc (-r) r)).prod μ) := by
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
  _ = ∫ y, ∫ x in Set.Ioc (-r) r, cexp (x * y * I) ∂volume ∂μ
      - ∫ y, ∫ x in Set.Ioc r (-r), cexp (x * y * I) ∂volume ∂μ := by
    rw [intervalIntegral]
    congr 1
    · rw [integral_integral_swap]
      exact h_int r
    · rw [integral_integral_swap]
      convert h_int (-r)
      simp
  _ = ∫ y, ∫ x in -r..r, cexp (x * y * I) ∂volume ∂μ:= by
    have h_le (y : ℝ) a : ‖∫ (x : ℝ) in Set.Ioc (-a) a, cexp (x * y * I)‖ ≤ max (a + a) 0 := by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      norm_cast
      simp_rw [norm_exp_ofReal_mul_I]
      simp
    rw [← integral_sub]
    · congr
    · refine Integrable.mono' (integrable_const (max (r + r) 0)) ?_
        (ae_of_all _ fun y ↦ h_le y r)
      refine StronglyMeasurable.aestronglyMeasurable ?_
      refine StronglyMeasurable.integral_prod_left (f := fun (x y : ℝ) ↦ cexp (x * y * I)) ?_
      exact Measurable.stronglyMeasurable (by fun_prop)
    · refine Integrable.mono' (integrable_const (max (-r + -r) 0)) ?_
        (ae_of_all _ fun y ↦ ?_)
      · refine StronglyMeasurable.aestronglyMeasurable ?_
        refine StronglyMeasurable.integral_prod_left (f := fun (x y : ℝ) ↦ cexp (x * y * I)) ?_
        exact Measurable.stronglyMeasurable (by fun_prop)
      · convert h_le y (-r) using 2
        simp
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
    rw [integral_exp_Icc_eq_sinc]
    split_ifs with hry
    · simp [hry]
    have hy : y ≠ 0 := fun hy ↦ hry (by simp [hy])
    norm_cast
    field_simp
    ring_nf
  _ = 2 * r * ∫ x, sinc (r * x) ∂μ := by
    norm_cast
    rw [integral_complex_ofReal, ← integral_const_mul]

lemma integrable_sinc_const_mul {μ : Measure ℝ} [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun x ↦ sinc (r * x)) μ :=
  (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable (by fun_prop)).mp
    integrable_sinc

lemma measure_abs_ge_le_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
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

omit [SecondCountableTopology E] in
lemma measure_abs_inner_ge_le_charFun {μ : Measure E} [IsProbabilityMeasure μ]
    {a : E} {r : ℝ} (hr : 0 < r) :
    μ.real {x | r < |⟪a, x⟫|}
      ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun μ (t • a)‖ := by
  have : IsProbabilityMeasure (μ.map (fun x ↦ ⟪a, x⟫)) := isProbabilityMeasure_map (by fun_prop)
  rw [Measure.real_def]
  convert measure_abs_ge_le_charFun (μ := μ.map (fun x ↦ ⟪a, x⟫)) hr with x
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

end bounds

end InnerProductSpace

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  {μ : Measure E} {ν : Measure F}

/-- The characteristic function of a measure in a normed space, function from `Dual ℝ E` to `ℂ`
with `charFunDual μ L = ∫ v, exp (L v * I) ∂μ`. -/
noncomputable
def charFunDual (μ : Measure E) (L : Dual ℝ E) : ℂ := ∫ v, probCharDual L v ∂μ

lemma charFunDual_apply (L : Dual ℝ E) : charFunDual μ L = ∫ v, exp (L v * I) ∂μ := rfl

lemma charFunDual_eq_charFun_map_one [OpensMeasurableSpace E] (L : Dual ℝ E) :
    charFunDual μ L = charFun (μ.map L) 1 := by
  rw [charFunDual_apply]
  have : ∫ x, cexp (L x * I) ∂μ = ∫ x, cexp (x * I) ∂(μ.map L) := by
    rw [integral_map]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp

lemma charFun_map_eq_charFunDual_smul [OpensMeasurableSpace E] (L : Dual ℝ E) (u : ℝ) :
    charFun (μ.map L) u = charFunDual μ (u • L) := by
  rw [charFunDual_apply]
  have : ∫ x, cexp ((u • L) x * I) ∂μ = ∫ x, cexp (u * x * I) ∂(μ.map L) := by
    rw [integral_map]
    · simp
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp

lemma charFun_eq_charFunDual_toDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mE : MeasurableSpace E} {μ : Measure E} (t : E) :
    charFun μ t = charFunDual μ (InnerProductSpace.toDualMap ℝ E t) := by
  simp [charFunDual_apply, charFun_apply, real_inner_comm]

lemma charFunDual_map [OpensMeasurableSpace E] [BorelSpace F] (L : E →L[ℝ] F) (L' : Dual ℝ F) :
    charFunDual (μ.map L) L' = charFunDual μ (L'.comp L) := by
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp

@[simp]
lemma charFunDual_dirac [OpensMeasurableSpace E] {x : E} (L : Dual ℝ E) :
    charFunDual (Measure.dirac x) L = cexp (L x * I) := by
  rw [charFunDual_apply, integral_dirac]

/-- The characteristic function of a product of measures is a product of
characteristic functions. -/
lemma charFunDual_prod [SFinite μ] [SFinite ν] (L : Dual ℝ (E × F)) :
    charFunDual (μ.prod ν) L
      = charFunDual μ (L.comp (.inl ℝ E F)) * charFunDual ν (L.comp (.inr ℝ E F)) := by
  let L₁ : Dual ℝ E := L.comp (.inl ℝ E F)
  let L₂ : Dual ℝ F := L.comp (.inr ℝ E F)
  simp_rw [charFunDual_apply, ← L.comp_inl_add_comp_inr, ofReal_add, add_mul,
    Complex.exp_add]
  rw [integral_prod_mul (f := fun x ↦ cexp ((L₁ x * I))) (g := fun x ↦ cexp ((L₂ x * I)))]

variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- If two finite measures have the same characteristic function, then they are equal. -/
theorem Measure.ext_of_charFunDual {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFunDual μ = charFunDual ν) :
    μ = ν := by
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one
    ?_ ?_ (fun L ↦ funext_iff.mp h L)
  · intro v hv
    rw [ne_eq, LinearMap.ext_iff]
    simp only [ContinuousLinearMap.toLinearMap₂_apply, LinearMap.zero_apply, not_forall]
    change ∃ L : Dual ℝ E, L v ≠ 0
    by_contra! h
    exact hv (NormedSpace.eq_zero_of_forall_dual_eq_zero _ h)
  · exact isBoundedBilinearMap_apply.symm.continuous

end NormedSpace

end MeasureTheory
