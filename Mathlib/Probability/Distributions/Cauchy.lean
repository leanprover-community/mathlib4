/-
Copyright (c) 2026 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib

/-! # Cauchy Distribution over ℝ

Define the Cauchy distribution over the reals.

## Main definitions
* `cauchyPDFReal`: the function `r x ↦ r * exp (-(r * x)` for `0 ≤ x`
  or `0` else, which is the probability density function of an exponential distribution with
  rate `r` (when `hr : 0 < r`).
* `cauchyPDF`: `ℝ≥0∞`-valued pdf,
  `exponentialPDF r = ENNReal.ofReal (cauchyPDFReal r)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `r`.

## Main results
* `cdf_expMeasure_eq`: Proof that the CDF of the exponential measure equals the
  known function given as `r x ↦ 1 - exp (- (r * x))` for `0 ≤ x` or `0` else.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Measure

namespace Probability

section CauchyPDF

/-- The pdf of the cauchy distribution depending on its location `x₀` and scale `γ` parameters. -/
noncomputable def cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ :=
  .pi⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹

lemma cauchyPDFReal_def (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
    cauchyPDFReal x₀ γ x  = .pi⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹ := by rfl

lemma cauchyPDFReal_def' (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) :
    cauchyPDFReal x₀ γ x = .pi⁻¹ * γ⁻¹ * (1 + ((x - x₀) / γ) ^ 2)⁻¹ := by sorry

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞`. -/
noncomputable def cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cauchyPDFReal x₀ γ x)

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

/-- The pdf of the cauchy distribution integrates to 1 -/
@[simp]
lemma lintegral_cauchyPDF_eq_one (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫⁻ x, cauchyPDF x₀ γ x = 1 := by
  unfold cauchyPDF
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (by filter_upwards with x; simpa using by positivity [cauchyPDF_pos x₀ hγ x])
    (by fun_prop)]
  simp [cauchyPDFReal_def', NNReal.coe_inv, integral_const_mul,
    integral_sub_right_eq_self (f := fun x : ℝ ↦ (1 + (x / ↑γ) ^ 2)⁻¹),
    integral_comp_div (g := fun x : ℝ ↦ (1 + x ^ 2)⁻¹)]
  field

@[fun_prop]
lemma integrable_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    Integrable (cauchyPDFReal x₀ γ) := by
  rw [← lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards with x; simpa using by positivity [cauchyPDF_pos x₀ hγ x])]
  simp [← cauchyPDF_def, lintegral_cauchyPDF_eq_one x₀ hγ]

-- INTEGRAL CAUCHYREALPDF PROOF

end CauchyPDF

section CauchyMeasure

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
