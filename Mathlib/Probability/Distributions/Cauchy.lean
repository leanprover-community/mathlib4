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

@[expose] public section

open scoped Real ENNReal NNReal

open MeasureTheory Measure

namespace Probability

section CauchyPDF

/-- The pdf of the cauchy distribution depending on its location `x₀` and scale `γ` parameters. -/
noncomputable def cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ :=
  π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹

@[simp]
lemma cauchyPDFReal_scale_zero (x₀ : ℝ) : cauchyPDFReal x₀ 0 = 0 := by
  ext
  simp [cauchyPDFReal]

lemma cauchyPDFReal_def (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
    cauchyPDFReal x₀ γ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹ := by rfl

lemma cauchyPDFReal_def' (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
    cauchyPDFReal x₀ γ x = π⁻¹ * γ⁻¹ * (1 + ((x - x₀) / γ) ^ 2)⁻¹ := by
  rw [cauchyPDFReal_def]
  by_cases h : γ = 0
  · simp [h]
  simp
  field

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞`. -/
noncomputable def cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cauchyPDFReal x₀ γ x)

@[simp]
lemma cauchyPDF_scale_zero (x₀ : ℝ) : cauchyPDF x₀ 0 = 0 := by
  ext
  simp [cauchyPDF]

lemma cauchyPDF_def (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
  cauchyPDF x₀ γ x = ENNReal.ofReal (cauchyPDFReal x₀ γ x) := by rfl

@[fun_prop]
lemma measurable_cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) : Measurable (cauchyPDFReal x₀ γ) := by
  unfold cauchyPDFReal
  fun_prop

@[fun_prop]
lemma stronglyMeasurable_cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) :
    StronglyMeasurable (cauchyPDFReal x₀ γ) := by fun_prop

@[fun_prop]
lemma measurable_cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) : Measurable (cauchyPDF x₀ γ) := by
  unfold cauchyPDF
  fun_prop

@[fun_prop]
lemma stronglyMeasurable_cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) :
    StronglyMeasurable (cauchyPDF x₀ γ) := by fun_prop

/-- `cauchyPDFReal` is positive for `γ > 0`. -/
lemma cauchyPDF_pos (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) : 0 < cauchyPDFReal x₀ γ x := by
  rw [cauchyPDFReal_def]
  positivity

set_option backward.isDefEq.respectTransparency false in
lemma integral_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫ x, cauchyPDFReal x₀ γ x = 1 := by
  simp [cauchyPDFReal_def', NNReal.coe_inv, integral_const_mul,
    integral_sub_right_eq_self (f := fun x : ℝ ↦ (1 + (x / ↑γ) ^ 2)⁻¹),
    integral_comp_div (g := fun x : ℝ ↦ (1 + x ^ 2)⁻¹)]
  field

@[fun_prop]
lemma integrable_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} :
    Integrable (cauchyPDFReal x₀ γ) := by
  by_cases! h : γ = 0
  · simp only [h, cauchyPDFReal_scale_zero]
    exact integrable_zero _ _ _
  apply Integrable.of_integral_ne_zero
  simp [h, integral_cauchyPDFReal]

/-- The pdf of the cauchy distribution integrates to 1. -/
@[simp]
lemma lintegral_cauchyPDF_eq_one (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫⁻ x, cauchyPDF x₀ γ x = 1 := by
  unfold cauchyPDF
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x ↦ (cauchyPDF_pos x₀ hγ x).le) (by fun_prop), integral_cauchyPDFReal x₀ hγ]

end CauchyPDF

section CauchyMeasure

/-- A Cauchy distribution on `ℝ` with location parameter `x₀` and scale parameter `γ`. -/
noncomputable def cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) : Measure ℝ :=
  if γ = 0 then dirac x₀ else volume.withDensity (cauchyPDF x₀ γ)

lemma cauchyMeasure_of_scale_ne_zero (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    cauchyMeasure x₀ γ = volume.withDensity (cauchyPDF x₀ γ) := if_neg hγ

@[simp]
lemma cauchyMeasure_zero_scale (x₀ : ℝ) : cauchyMeasure x₀ 0 = dirac x₀ := if_pos rfl

instance instIsProbabilityMeasure_cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) :
    IsProbabilityMeasure (cauchyMeasure x₀ γ) where
  measure_univ := by by_cases h : γ = 0 <;> simp [cauchyMeasure_of_scale_ne_zero, h]

end CauchyMeasure

end Probability
