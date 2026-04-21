/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Cauchy Distribution over ℝ

Define the Cauchy distribution with location parameter `x₀` and scale parameter `γ`.

Note that we use "location" and "scale" to refer to these parameters in theorem names.

## Main definition

* `cauchyPDFReal`: the function `x₀ γ x ↦ π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹`,
  which is the probability density function of a Cauchy distribution with location parameter `x₀`
  and scale parameter `γ` (when `γ ≠ 0`).
* `cauchyPDF`: `ℝ≥0∞`-valued pdf, `cauchyPDF μ v x = ENNReal.ofReal (cauchyPDFReal μ v x)`.
* `cauchyMeasure`: a Cauchy measure on `ℝ`, parametrized by a location parameter `x₀ : ℝ` and a
  scale parameter `γ : ℝ≥0`.  If `γ = 0`, this is `dirac x₀`, otherwise it is defined as the
  measure with density `cauchyPDF x₀ γ` with respect to the Lebesgue measure.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped Real ENNReal NNReal

open MeasureTheory Measure

namespace ProbabilityTheory

section CauchyPDF

/-- The pdf of the cauchy distribution depending on its location `x₀` and scale `γ` parameters. -/
noncomputable def cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ :=
  π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹

@[deprecated (since := "2026-03-06")] alias _root_Probability.CauchyPDFReal := cauchyPDFReal

@[simp]
lemma cauchyPDFReal_scale_zero (x₀ : ℝ) : cauchyPDFReal x₀ 0 = 0 := by
  ext
  simp [cauchyPDFReal]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_scale_zero := cauchyPDFReal_scale_zero

lemma cauchyPDFReal_def (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
    cauchyPDFReal x₀ γ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹ := by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def := cauchyPDFReal_def

lemma cauchyPDFReal_def' (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
    cauchyPDFReal x₀ γ x = π⁻¹ * γ⁻¹ * (1 + ((x - x₀) / γ) ^ 2)⁻¹ := by
  rw [cauchyPDFReal_def]
  by_cases h : γ = 0
  · simp [h]
  simp
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def' := cauchyPDFReal_def'

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞`. -/
noncomputable def cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cauchyPDFReal x₀ γ x)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF := cauchyPDF

@[simp]
lemma cauchyPDF_scale_zero (x₀ : ℝ) : cauchyPDF x₀ 0 = 0 := by
  ext
  simp [cauchyPDF]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_scale_zero := cauchyPDF_scale_zero

lemma cauchyPDF_def (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
  cauchyPDF x₀ γ x = ENNReal.ofReal (cauchyPDFReal x₀ γ x) := by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_def := cauchyPDF_def

@[fun_prop]
lemma measurable_cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) : Measurable (cauchyPDFReal x₀ γ) := by
  unfold cauchyPDFReal
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDFReal := measurable_cauchyPDFReal

@[fun_prop]
lemma stronglyMeasurable_cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) :
    StronglyMeasurable (cauchyPDFReal x₀ γ) := by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDFReal := stronglyMeasurable_cauchyPDFReal

@[fun_prop]
lemma measurable_cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) : Measurable (cauchyPDF x₀ γ) := by
  unfold cauchyPDF
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDF := measurable_cauchyPDF

@[fun_prop]
lemma stronglyMeasurable_cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) :
    StronglyMeasurable (cauchyPDF x₀ γ) := by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDF := stronglyMeasurable_cauchyPDF

/-- `cauchyPDFReal` is positive for `γ > 0`. -/
lemma cauchyPDF_pos (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) : 0 < cauchyPDFReal x₀ γ x := by
  rw [cauchyPDFReal_def]
  positivity

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyPDF_pos := cauchyPDF_pos

lemma integral_cauchyPDFReal_eq_one (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫ x, cauchyPDFReal x₀ γ x = 1 := by
  simp [cauchyPDFReal_def', NNReal.coe_inv, integral_const_mul,
    integral_sub_right_eq_self (f := fun x : ℝ ↦ (1 + (x / ↑γ) ^ 2)⁻¹),
    integral_comp_div (g := fun x : ℝ ↦ (1 + x ^ 2)⁻¹)]
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integral_cauchyPDFReal := integral_cauchyPDFReal_eq_one

@[fun_prop]
lemma integrable_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} :
    Integrable (cauchyPDFReal x₀ γ) := by
  by_cases! h : γ = 0
  · simp only [h, cauchyPDFReal_scale_zero]
    exact integrable_zero _ _ _
  apply Integrable.of_integral_ne_zero
  simp [h, integral_cauchyPDFReal_eq_one]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integrable_cauchyPDFReal := integrable_cauchyPDFReal

/-- The pdf of the cauchy distribution integrates to 1. -/
@[simp]
lemma lintegral_cauchyPDF_eq_one (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫⁻ x, cauchyPDF x₀ γ x = 1 := by
  unfold cauchyPDF
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x ↦ (cauchyPDF_pos x₀ hγ x).le) (by fun_prop),
    integral_cauchyPDFReal_eq_one x₀ hγ]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.lintegral_cauchyPDF_eq_one := lintegral_cauchyPDF_eq_one

end CauchyPDF

section CauchyMeasure

/-- A Cauchy distribution on `ℝ` with location parameter `x₀` and scale parameter `γ`. -/
noncomputable def cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) : Measure ℝ :=
  if γ = 0 then dirac x₀ else volume.withDensity (cauchyPDF x₀ γ)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure := cauchyMeasure

lemma cauchyMeasure_of_scale_ne_zero (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    cauchyMeasure x₀ γ = volume.withDensity (cauchyPDF x₀ γ) := if_neg hγ

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_of_scale_ne_zero := cauchyMeasure_of_scale_ne_zero

@[simp]
lemma cauchyMeasure_zero_scale (x₀ : ℝ) : cauchyMeasure x₀ 0 = dirac x₀ := if_pos rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_zero_scale := cauchyMeasure_zero_scale

instance instIsProbabilityMeasure_cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) :
    IsProbabilityMeasure (cauchyMeasure x₀ γ) where
  measure_univ := by by_cases h : γ = 0 <;> simp [cauchyMeasure_of_scale_ne_zero, h]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.instIsProbabilityMeasure_cauchyMeasure :=
  instIsProbabilityMeasure_cauchyMeasure

end CauchyMeasure

end ProbabilityTheory
