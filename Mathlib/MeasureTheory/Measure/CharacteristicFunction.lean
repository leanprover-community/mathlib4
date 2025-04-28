/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel, Rémy Degenne, Thomas Zhu
-/
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.Normed.Module.Dual

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

## Main statements

* `ext_of_integral_char_eq`: Assume `e` and `L` are non-trivial. If the integrals of `char`
  with respect to two finite measures `P` and `P'` coincide, then `P = P'`.
* `Measure.ext_of_charFun`: If the characteristic functions `charFun` of two finite measures
  `μ` and `ν` on a complete second-countable inner product space coincide, then `μ = ν`.

-/

open BoundedContinuousFunction RealInnerProductSpace Real Complex ComplexConjugate

namespace BoundedContinuousFunction

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bounded continuous map `x ↦ exp(⟪x, t⟫ * I)`. -/
noncomputable
def innerProbChar (t : E) : E →ᵇ ℂ :=
  char continuous_probChar (L := bilinFormOfRealInner) continuous_inner t

lemma innerProbChar_apply (t x : E) : innerProbChar t x = exp (⟪x, t⟫ * I) := rfl

@[simp]
lemma innerProbChar_zero : innerProbChar (0 : E) = 1 := by simp [innerProbChar]

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

@[measurability]
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

lemma integral_conv {E F : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    {μ ν : Measure E} [SFinite μ] [SFinite ν]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : Integrable f (μ ∗ ν)) :
    ∫ x, f x ∂(μ ∗ ν) = ∫ x, ∫ y, f (x + y) ∂ν ∂μ := by
  unfold Measure.conv
  rw [integral_map (by fun_prop) hf.1, integral_prod]
  exact (integrable_map_measure hf.1 (by fun_prop)).mp hf

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

/-- The characteristic function of a convolution of measures
is the product of the respective characteristic functions. -/
lemma charFun_conv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E) :
    charFun (μ ∗ ν) t = charFun μ t * charFun ν t := by
  simp_rw [charFun_apply]
  rw [integral_conv]
  · simp_rw [inner_add_left]
    push_cast
    simp_rw [add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · -- todo: extract lemma about integrability wrt conv?
    unfold Measure.conv
    rw [integrable_map_measure]
    · apply (integrable_const (1 : ℝ)).mono
      · exact Measurable.aestronglyMeasurable <| by fun_prop
      · simp
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · fun_prop

end InnerProductSpace

lemma _root_.IsBoundedBilinearMap.symm {E F G 𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedBilinearMap 𝕜 (fun p ↦ f (p.2, p.1)) where
  add_left x₁ x₂ y := h.add_right _ _ _
  smul_left c x y := h.smul_right _ _ _
  add_right x y₁ y₂ := h.add_left _ _ _
  smul_right c x y := h.smul_left _ _ _
  bound := by
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, fun x y ↦ (hC y x).trans_eq (by ring)⟩

lemma _root_.ContinuousLinearMap.comp_inl_add_comp_inr
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E × F →L[ℝ] ℝ) (v : E × F) :
    L.comp (.inl ℝ E F) v.1 + L.comp (.inr ℝ E F) v.2 = L v := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← ContinuousLinearMap.map_add]
  simp

namespace BoundedContinuousFunction

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bounded continuous function `x ↦ exp (L x * I)`, for a continuous linear form `L`. -/
noncomputable
def probCharCLM (L : E →L[ℝ] ℝ) : E →ᵇ ℂ :=
  char continuous_probChar (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₂)
    isBoundedBilinearMap_apply.symm.continuous L

lemma probCharCLM_apply (L : E →L[ℝ] ℝ) (x : E) : probCharCLM L x = exp (L x * I) := rfl

@[simp]
lemma probCharCLM_zero : probCharCLM (0 : E →L[ℝ] ℝ) = 1 := by simp [probCharCLM]

end BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  {μ : Measure E} {ν : Measure F}

/-- The characteristic function of a measure in a normed space, function from `E →L[ℝ] ℝ` to `ℂ`
with `charFunCLM μ L = ∫ v, exp (L v * I) ∂μ`. -/
noncomputable
def charFunCLM (μ : Measure E) (L : E →L[ℝ] ℝ) : ℂ :=
  ∫ v, BoundedContinuousFunction.probCharCLM L v ∂μ

lemma charFunCLM_apply (L : E →L[ℝ] ℝ) : charFunCLM μ L = ∫ v, exp (L v * I) ∂μ := rfl

@[simp]
lemma charFunCLM_dirac [OpensMeasurableSpace E] {x : E} (L : E →L[ℝ] ℝ) :
    charFunCLM (Measure.dirac x) L = cexp (L x * I) := by
  rw [charFunCLM_apply, integral_dirac]

lemma charFunCLM_prod [SFinite μ] [SFinite ν] (L : E × F →L[ℝ] ℝ) :
    charFunCLM (μ.prod ν) L
      = charFunCLM μ (L.comp (.inl ℝ E F)) * charFunCLM ν (L.comp (.inr ℝ E F)) := by
  let L₁ : E →L[ℝ] ℝ := L.comp (.inl ℝ E F)
  let L₂ : F →L[ℝ] ℝ := L.comp (.inr ℝ E F)
  simp_rw [charFunCLM_apply, ← L.comp_inl_add_comp_inr, ofReal_add, add_mul,
    Complex.exp_add]
  rw [integral_prod_mul (f := fun x ↦ cexp ((L₁ x * I))) (g := fun x ↦ cexp ((L₂ x * I)))]

lemma charFunCLM_eq_charFun_map_one [OpensMeasurableSpace E] (L : E →L[ℝ] ℝ) :
    charFunCLM μ L = charFun (μ.map L) 1 := by
  rw [charFunCLM_apply]
  have : ∫ x, cexp (L x * I) ∂μ = ∫ x, cexp (x * I) ∂(μ.map L) := by
    rw [integral_map]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp

lemma charFun_map_eq_charFunCLM_smul [OpensMeasurableSpace E] (L : E →L[ℝ] ℝ) (u : ℝ) :
    charFun (μ.map L) u = charFunCLM μ (u • L) := by
  rw [charFunCLM_apply]
  have : ∫ x, cexp ((u • L) x * I) ∂μ = ∫ x, cexp (u * x * I) ∂(μ.map L) := by
    rw [integral_map]
    · simp
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp

lemma charFunCLM_map [OpensMeasurableSpace E] [BorelSpace F] {μ : Measure E}
    (L : E →L[ℝ] F) (L' : F →L[ℝ] ℝ) :
    charFunCLM (μ.map L) L' = charFunCLM μ (L'.comp L) := by
  rw [charFunCLM_eq_charFun_map_one, charFunCLM_eq_charFun_map_one,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp

variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- If two finite measures have the same characteristic function, then they are equal. -/
theorem ext_of_charFunCLM {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFunCLM μ = charFunCLM ν) :
    μ = ν := by
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one
    ?_ ?_ (fun L ↦ funext_iff.mp h L)
  · intro v hv
    rw [ne_eq, LinearMap.ext_iff]
    simp only [ContinuousLinearMap.toLinearMap₂_apply, LinearMap.zero_apply, not_forall]
    change ∃ L : E →L[ℝ] ℝ, L v ≠ 0
    by_contra! h
    exact hv (NormedSpace.eq_zero_of_forall_dual_eq_zero _ h)
  · exact isBoundedBilinearMap_apply.symm.continuous

end MeasureTheory
