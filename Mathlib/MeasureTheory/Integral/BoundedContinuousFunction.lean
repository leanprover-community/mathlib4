/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Integration of bounded continuous functions

In this file, some results are collected about integrals of bounded continuous functions. They are
mostly specializations of results in general integration theory, but they are used directly in this
specialized form in some other files, in particular in those related to the topology of weak
convergence of probability measures and finite measures.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

namespace BoundedContinuousFunction

section NNRealValued

lemma apply_le_nndist_zero {X : Type*} [TopologicalSpace X] (f : X →ᵇ ℝ≥0) (x : X) :
    f x ≤ nndist 0 f := by
  convert nndist_coe_le_nndist x
  simp only [coe_zero, Pi.zero_apply, NNReal.nndist_zero_eq_val]

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

lemma lintegral_le_edist_mul (f : X →ᵇ ℝ≥0) (μ : Measure X) :
    (∫⁻ x, f x ∂μ) ≤ edist 0 f * (μ Set.univ) :=
  le_trans (lintegral_mono (fun x ↦ ENNReal.coe_le_coe.mpr (f.apply_le_nndist_zero x))) (by simp)

theorem measurable_coe_ennreal_comp [OpensMeasurableSpace X] (f : X →ᵇ ℝ≥0) :
    Measurable fun x ↦ (f x : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp f.continuous.measurable

variable (μ : Measure X) [IsFiniteMeasure μ]

theorem lintegral_lt_top_of_nnreal (f : X →ᵇ ℝ≥0) : ∫⁻ x, f x ∂μ < ∞ := by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  refine ⟨nndist f 0, fun x ↦ ?_⟩
  have key := BoundedContinuousFunction.NNReal.upper_bound f x
  rwa [ENNReal.coe_le_coe]

theorem integrable_of_nnreal [OpensMeasurableSpace X] (f : X →ᵇ ℝ≥0) :
    Integrable (((↑) : ℝ≥0 → ℝ) ∘ ⇑f) μ := by
  refine ⟨(NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable, ?_⟩
  simp only [hasFiniteIntegral_iff_enorm, Function.comp_apply, NNReal.enorm_eq]
  exact lintegral_lt_top_of_nnreal _ f

theorem integral_eq_integral_nnrealPart_sub [OpensMeasurableSpace X] (f : X →ᵇ ℝ) :
    ∫ x, f x ∂μ = (∫ x, (f.nnrealPart x : ℝ) ∂μ) - ∫ x, ((-f).nnrealPart x : ℝ) ∂μ := by
  simp only [f.self_eq_nnrealPart_sub_nnrealPart_neg, Pi.sub_apply, integral_sub,
             integrable_of_nnreal]
  simp only [Function.comp_apply]

theorem lintegral_of_real_lt_top (f : X →ᵇ ℝ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ∞ := lintegral_lt_top_of_nnreal _ f.nnrealPart

theorem toReal_lintegral_coe_eq_integral [OpensMeasurableSpace X] (f : X →ᵇ ℝ≥0) (μ : Measure X) :
    (∫⁻ x, (f x : ℝ≥0∞) ∂μ).toReal = ∫ x, (f x : ℝ) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae _ (by simpa [Function.comp_apply] using
        (NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable)]
  · simp only [ENNReal.ofReal_coe_nnreal]
  · exact Eventually.of_forall (by simp)

end NNRealValued

section BochnerIntegral

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable (μ : Measure X)
variable {E : Type*} [NormedAddCommGroup E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
lemma lintegral_nnnorm_le (f : X →ᵇ E) :
    ∫⁻ x, ‖f x‖₊ ∂μ ≤ ‖f‖₊ * (μ Set.univ) := by
  calc  ∫⁻ x, ‖f x‖₊ ∂μ
    _ ≤ ∫⁻ _, ‖f‖₊ ∂μ       := by gcongr; apply nnnorm_coe_le_nnnorm
    _ = ‖f‖₊ * (μ Set.univ) := by rw [lintegral_const]

variable [OpensMeasurableSpace X] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
lemma integrable [IsFiniteMeasure μ] (f : X →ᵇ E) :
    Integrable f μ := by
  refine ⟨f.continuous.measurable.aestronglyMeasurable, (hasFiniteIntegral_def _ _).mp ?_⟩
  calc  ∫⁻ x, ‖f x‖₊ ∂μ
    _ ≤ ‖f‖₊ * (μ Set.univ) := f.lintegral_nnnorm_le μ
    _ < ∞                   := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ Set.univ)

variable [NormedSpace ℝ E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
lemma norm_integral_le_mul_norm [IsFiniteMeasure μ] (f : X →ᵇ E) :
    ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖ := by
  calc  ‖∫ x, f x ∂μ‖
    _ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _, ‖f‖ ∂μ := ?_
    _ = μ.real Set.univ • ‖f‖ := by rw [integral_const]
  apply integral_mono _ (integrable_const ‖f‖) (fun x ↦ f.norm_coe_le_norm x) -- NOTE: `gcongr`?
  exact (integrable_norm_iff f.continuous.measurable.aestronglyMeasurable).mpr (f.integrable μ)

lemma norm_integral_le_norm [IsProbabilityMeasure μ] (f : X →ᵇ E) :
    ‖∫ x, f x ∂μ‖ ≤ ‖f‖ := by
  convert f.norm_integral_le_mul_norm μ
  simp

lemma isBounded_range_integral
    {ι : Type*} (μs : ι → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (f : X →ᵇ E) :
    Bornology.IsBounded (Set.range (fun i ↦ ∫ x, f x ∂(μs i))) := by
  apply isBounded_iff_forall_norm_le.mpr ⟨‖f‖, fun v hv ↦ ?_⟩
  obtain ⟨i, hi⟩ := hv
  rw [← hi]
  apply f.norm_integral_le_norm (μs i)

end BochnerIntegral

section RealValued

variable {X : Type*} [TopologicalSpace X]
variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

lemma integral_add_const (f : X →ᵇ ℝ) (c : ℝ) :
    ∫ x, (f + const X c) x ∂μ = ∫ x, f x ∂μ + μ.real Set.univ • c := by
  simp [integral_add (f.integrable _) (integrable_const c)]

lemma integral_const_sub (f : X →ᵇ ℝ) (c : ℝ) :
    ∫ x, (const X c - f) x ∂μ = μ.real Set.univ • c - ∫ x, f x ∂μ := by
  simp [integral_sub (integrable_const c) (f.integrable _)]

end RealValued

section tendsto_integral

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

lemma tendsto_integral_of_forall_limsup_integral_le_integral {ι : Type*} {L : Filter ι}
    {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι → Measure X} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : X →ᵇ ℝ, 0 ≤ f → L.limsup (fun i ↦ ∫ x, f x ∂(μs i)) ≤ ∫ x, f x ∂μ)
    (f : X →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, f x ∂(μs i)) L (𝓝 (∫ x, f x ∂μ)) := by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply tendsto_of_le_liminf_of_limsup_le _ _ bdd_above bdd_below
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_const_sub L (fun i ↦ ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, _root_.sub_le_sub_iff_left ‖f‖] at key
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_add_const L (fun i ↦ ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, add_le_add_iff_right] at key

lemma tendsto_integral_of_forall_integral_le_liminf_integral {ι : Type*} {L : Filter ι}
    {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι → Measure X} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : X →ᵇ ℝ, 0 ≤ f → ∫ x, f x ∂μ ≤ L.liminf (fun i ↦ ∫ x, f x ∂(μs i)))
    (f : X →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, f x ∂(μs i)) L (𝓝 (∫ x, f x ∂μ)) := by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply @tendsto_of_le_liminf_of_limsup_le ℝ ι _ _ _ L (fun i ↦ ∫ x, f x ∂(μs i)) (∫ x, f x ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_add_const L (fun i ↦ ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i ↦ ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, sub_le_sub_iff_left] at key
  · exact bdd_above
  · exact bdd_below

end tendsto_integral --section

end BoundedContinuousFunction
