/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel, Rémy Degenne, Thomas Zhu
-/
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Pi
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
  WithLp

open scoped ENNReal

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
def probCharDual (L : StrongDual ℝ F) : F →ᵇ ℂ :=
  char continuous_probChar
    (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₁₂)
    isBoundedBilinearMap_apply.symm.continuous L

lemma probCharDual_apply (L : StrongDual ℝ F) (x : F) : probCharDual L x = exp (L x * I) := rfl

@[simp]
lemma probCharDual_zero : probCharDual (0 : StrongDual ℝ F) = 1 := by simp [probCharDual]

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
  simp only [MeasureTheory.integral_const_mul, mul_eq_mul_left_iff]
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
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
lemma charFun_dirac [OpensMeasurableSpace E] {x : E} (t : E) :
    charFun (Measure.dirac x) t = cexp (⟪x, t⟫ * I) := by
  rw [charFun_apply, integral_dirac]

lemma charFun_map_add_const [BorelSpace E] (r t : E) :
    charFun (μ.map (· + r)) t = charFun μ t * cexp (⟪r, t⟫ * I) := by
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop),
    ← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  rw [inner_add_left]
  simp only [ofReal_add]
  ring

lemma charFun_map_const_add [BorelSpace E] (r t : E) :
    charFun (μ.map (r + ·)) t = charFun μ t * cexp (⟪r, t⟫ * I) := by
  simp_rw [add_comm r]
  exact charFun_map_add_const _ _

variable [BorelSpace E] [SecondCountableTopology E]

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
  · simp [inner_add_left, add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] {mE : MeasurableSpace E}
    {mF : MeasurableSpace F}

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Hilbert spaces, see `charFunDual_prod`
for the Banach space version. -/
lemma charFun_prod {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν]
    (t : WithLp 2 (E × F)) :
    charFun ((μ.prod ν).map (toLp 2)) t =
      charFun μ (ofLp t).1 * charFun ν (ofLp t).2 := by
  simp_rw [charFun, prod_inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_prod_mul,
    integral_map_equiv]
  simp [ofReal_add, add_mul, Complex.exp_add]

variable [CompleteSpace E] [CompleteSpace F] [SecondCountableTopology E] [SecondCountableTopology F]
    [BorelSpace E] [BorelSpace F]

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Hilbert spaces, see `charFunDual_eq_prod_iff`
for the Banach space version. -/
lemma charFun_eq_prod_iff {μ : Measure E} {ν : Measure F} {ξ : Measure (E × F)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    (∀ t, charFun (ξ.map (toLp 2)) t = charFun μ (ofLp t).1 * charFun ν (ofLp t).2) ↔
    ξ = μ.prod ν where
  mp h := by
    refine (MeasurableEquiv.toLp 2 (E × F)).map_measurableEquiv_injective
      <| Measure.ext_of_charFun <| funext fun t ↦ ?_
    rw [MeasurableEquiv.coe_toLp, h, charFun_prod]
  mpr h := by rw [h]; exact charFun_prod

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Hilbert spaces, see `charFunDual_pi`
for the Banach space version. -/
lemma charFun_pi {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (t : PiLp 2 E) :
    charFun ((Measure.pi μ).map (toLp 2)) t = ∏ i, charFun (μ i) (t i) := by
  simp_rw [charFun, PiLp.inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_fintype_prod_eq_prod,
    integral_map_equiv]
  simp [ofReal_sum, Finset.sum_mul, Complex.exp_sum]

variable [∀ i, CompleteSpace (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Hilbert spaces, see `charFunDual_eq_pi_iff`
for the Banach space version. -/
lemma charFun_eq_pi_iff {μ : (i : ι) → Measure (E i)} {ν : Measure (Π i, E i)}
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] :
    (∀ t, charFun (ν.map (toLp 2)) t = ∏ i, charFun (μ i) (t i)) ↔ ν = Measure.pi μ where
  mp h := by
    refine (MeasurableEquiv.toLp 2 (Π i, E i)).map_measurableEquiv_injective
      <| Measure.ext_of_charFun <| funext fun t ↦ ?_
    rw [MeasurableEquiv.coe_toLp, h, charFun_pi]
  mpr h := by rw [h]; exact charFun_pi

end InnerProductSpace

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  {μ : Measure E} {ν : Measure F}

/-- The characteristic function of a measure in a normed space, function from `StrongDual ℝ E` to
`ℂ` with `charFunDual μ L = ∫ v, exp (L v * I) ∂μ`. -/
noncomputable
def charFunDual (μ : Measure E) (L : StrongDual ℝ E) : ℂ := ∫ v, probCharDual L v ∂μ

lemma charFunDual_apply (L : StrongDual ℝ E) : charFunDual μ L = ∫ v, exp (L v * I) ∂μ := rfl

lemma charFunDual_eq_charFun_map_one [OpensMeasurableSpace E] (L : StrongDual ℝ E) :
    charFunDual μ L = charFun (μ.map L) 1 := by
  rw [charFunDual_apply]
  have : ∫ x, cexp (L x * I) ∂μ = ∫ x, cexp (x * I) ∂(μ.map L) := by
    rw [integral_map]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp

lemma charFun_map_eq_charFunDual_smul [OpensMeasurableSpace E] (L : StrongDual ℝ E) (u : ℝ) :
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

lemma charFunDual_map [OpensMeasurableSpace E] [BorelSpace F] (L : E →L[ℝ] F)
    (L' : StrongDual ℝ F) : charFunDual (μ.map L) L' = charFunDual μ (L'.comp L) := by
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp

@[simp]
lemma charFunDual_dirac [OpensMeasurableSpace E] {x : E} (L : StrongDual ℝ E) :
    charFunDual (Measure.dirac x) L = cexp (L x * I) := by
  rw [charFunDual_apply, integral_dirac]

lemma charFunDual_map_add_const [BorelSpace E] (r : E) (L : StrongDual ℝ E) :
    charFunDual (μ.map (· + r)) L = charFunDual μ L * cexp (L r * I) := by
  rw [charFunDual_apply, charFunDual_apply, integral_map (by fun_prop) (by fun_prop),
    ← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  simp only [map_add, ofReal_add]
  ring

lemma charFunDual_map_const_add [BorelSpace E] (r : E) (L : StrongDual ℝ E) :
    charFunDual (μ.map (r + ·)) L = charFunDual μ L * cexp (L r * I) := by
  simp_rw [add_comm r]
  exact charFunDual_map_add_const _ _

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Banach spaces, see `charFun_prod`
for the Hilbert space version. -/
lemma charFunDual_prod [SFinite μ] [SFinite ν] (L : StrongDual ℝ (E × F)) :
    charFunDual (μ.prod ν) L
      = charFunDual μ (L.comp (.inl ℝ E F)) * charFunDual ν (L.comp (.inr ℝ E F)) := by
  simp_rw [charFunDual_apply, ← L.comp_inl_add_comp_inr, ofReal_add, add_mul,
    Complex.exp_add, ← integral_prod_mul]

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is `charFunDual_prod` for `WithLp`.
See `charFun_prod` for the Hilbert space version. -/
lemma charFunDual_prod' (p : ℝ≥0∞) [Fact (1 ≤ p)] [SFinite μ] [SFinite ν]
    (L : StrongDual ℝ (WithLp p (E × F))) :
    charFunDual ((μ.prod ν).map (toLp p)) L =
      charFunDual μ (L.comp
        ((prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inl ℝ E F))) *
      charFunDual ν (L.comp
        ((prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inr ℝ E F))) := by
  simp_rw [charFunDual_apply, ← integral_prod_mul, ← Complex.exp_add, ← add_mul, ← ofReal_add,
    L.comp_apply, ← map_add, ContinuousLinearMap.comp_inl_add_comp_inr]
  rw [← MeasurableEquiv.coe_toLp, integral_map_equiv]
  simp

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Banach spaces, see `charFunDual_pi`
for the Hilbert space version. -/
lemma charFunDual_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (L : StrongDual ℝ (Π i, E i)) :
    charFunDual (Measure.pi μ) L =
      ∏ i, charFunDual (μ i) (L.comp (.single ℝ E i)) := by
  simp_rw [charFunDual_apply, ← L.sum_comp_single, ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    ← integral_fintype_prod_eq_prod]

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is `charFunDual_pi` for `PiLp`.
See `charFunDual_pi` for the Banach space version. -/
lemma charFunDual_pi' (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (L : StrongDual ℝ (PiLp p E)) :
    charFunDual ((Measure.pi μ).map (toLp p)) L =
      ∏ i, charFunDual (μ i) (L.comp
        ((PiLp.continuousLinearEquiv p ℝ E).symm.toContinuousLinearMap.comp (.single ℝ E i))) := by
  simp_rw [charFunDual_apply, ← integral_fintype_prod_eq_prod, ← Complex.exp_sum, ← Finset.sum_mul,
    ← ofReal_sum, L.comp_apply, ← map_sum, ContinuousLinearMap.sum_comp_single]
  rw [← MeasurableEquiv.coe_toLp, integral_map_equiv]
  simp

variable [BorelSpace E] [SecondCountableTopology E]

/-- If two finite measures have the same characteristic function, then they are equal. -/
theorem Measure.ext_of_charFunDual [CompleteSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFunDual μ = charFunDual ν) :
    μ = ν := by
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one
    ?_ ?_ (fun L ↦ funext_iff.mp h L)
  · intro v hv
    rw [ne_eq, LinearMap.ext_iff]
    simp only [ContinuousLinearMap.toLinearMap₁₂_apply, LinearMap.zero_apply, not_forall]
    change ∃ L : StrongDual ℝ E, L v ≠ 0
    by_contra! h
    exact hv (NormedSpace.eq_zero_of_forall_dual_eq_zero _ h)
  · exact isBoundedBilinearMap_apply.symm.continuous

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Banach spaces, see `charFun_eq_prod_iff`
for the Hilbert space version. -/
lemma charFunDual_eq_prod_iff [BorelSpace F] [SecondCountableTopology F] [CompleteSpace E]
    [CompleteSpace F] {ξ : Measure (E × F)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ξ] :
    (∀ L, charFunDual ξ L =
      charFunDual μ (L.comp (.inl ℝ E F)) * charFunDual ν (L.comp (.inr ℝ E F))) ↔
    ξ = μ.prod ν where
  mp h := by
    refine Measure.ext_of_charFunDual <| funext fun t ↦ ?_
    rw [h, charFunDual_prod]
  mpr h := by rw [h]; exact charFunDual_prod

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is `charFunDual_eq_prod_iff` for `WithLp`.
See `charFun_eq_prod_iff` for the Hilbert space version. -/
lemma charFunDual_eq_prod_iff' (p : ℝ≥0∞) [Fact (1 ≤ p)] [BorelSpace F]
    [SecondCountableTopology F] [CompleteSpace E] [CompleteSpace F] {ξ : Measure (E × F)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    (∀ L, charFunDual (ξ.map (toLp p)) L =
      charFunDual μ (L.comp
        ((WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inl ℝ E F))) *
      charFunDual ν (L.comp
        ((WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inr ℝ E F)))) ↔
    ξ = μ.prod ν where
  mp h := by
    refine (MeasurableEquiv.toLp p (E × F)).map_measurableEquiv_injective
      <| Measure.ext_of_charFunDual <| funext fun L ↦ ?_
    rw [MeasurableEquiv.coe_toLp, h, charFunDual_prod']
  mpr h := by rw [h]; exact charFunDual_prod' p

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Banach spaces, see `charFun_eq_pi_iff`
for the Hilbert space version. -/
lemma charFunDual_eq_pi_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}
    [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, CompleteSpace (E i)]
    {μ : (i : ι) → Measure (E i)} {ν : Measure (Π i, E i)} [∀ i, IsFiniteMeasure (μ i)]
    [IsFiniteMeasure ν] :
    (∀ L, charFunDual ν L = ∏ i, charFunDual (μ i) (L.comp (.single ℝ E i))) ↔
    ν = Measure.pi μ where
  mp h := by
    refine Measure.ext_of_charFunDual <| funext fun t ↦ ?_
    rw [h, charFunDual_pi]
  mpr h := by rw [h]; exact charFunDual_pi

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is `charFunDual_eq_pi_iff` for `PiLp`.
See `charFun_eq_pi_iff` for the Hilbert space version. -/
lemma charFunDual_eq_pi_iff' (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {mE : ∀ i, MeasurableSpace (E i)} [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    [∀ i, CompleteSpace (E i)] {μ : (i : ι) → Measure (E i)} {ν : Measure (Π i, E i)}
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] :
    (∀ L, charFunDual (ν.map (toLp p)) L =
      ∏ i, charFunDual (μ i) (L.comp
        ((PiLp.continuousLinearEquiv p ℝ E).symm.toContinuousLinearMap.comp (.single ℝ E i)))) ↔
    ν = Measure.pi μ where
  mp h := by
    refine (MeasurableEquiv.toLp p (Π i, E i)).map_measurableEquiv_injective
      <| Measure.ext_of_charFunDual <| funext fun L ↦ ?_
    rw [MeasurableEquiv.coe_toLp, h, charFunDual_pi']
  mpr h := by rw [h]; exact charFunDual_pi' p

/-- The characteristic function of a convolution of measures
is the product of the respective characteristic functions. -/
lemma charFunDual_conv {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (L : StrongDual ℝ E) : charFunDual (μ ∗ ν) L = charFunDual μ L * charFunDual ν L := by
  simp_rw [charFunDual_apply]
  rw [integral_conv]
  · simp [add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)

end NormedSpace

end MeasureTheory
