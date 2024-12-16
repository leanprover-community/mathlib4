/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments

/-!
# Linearly tilted measures

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open MeasureTheory Real

open scoped ENNReal InnerProductSpace

namespace ProbabilityTheory

variable {μ : Measure ℝ} {t : ℝ}

/-- Exponentially tilted measure. When `x ↦ exp (t * x)` is integrable, `μ.linTilted t` is the
probability measure with density with respect to `μ` proportional to `exp (t * x)`.
Otherwise it is 0.
-/
noncomputable
def _root_.MeasureTheory.Measure.linTilted (μ : Measure ℝ) (t : ℝ) : Measure ℝ := μ.tilted (t * ·)

/- API needed:
- zero measure
- zero E
- add measure?
- add E
- smul measure
- smul E, if exists
- order measure
- order E, if exists

- monotone function
- link to mgf / cgf

-/

instance : IsZeroOrProbabilityMeasure (μ.linTilted t) := by
  rw [Measure.linTilted]; infer_instance

@[simp]
lemma linTilted_zero_measure : (0 : Measure ℝ).linTilted t = 0 := by simp [Measure.linTilted]

@[simp]
lemma linTilted_zero' : μ.linTilted (0 : ℝ) = (μ Set.univ)⁻¹ • μ := by simp [Measure.linTilted]

@[simp]
lemma linTilted_zero [IsZeroOrProbabilityMeasure μ] : μ.linTilted (0 : ℝ) = μ := by
  rw [linTilted_zero']
  cases eq_zero_or_isProbabilityMeasure μ with
  | inl h => simp [h]
  | inr h => simp [h]

lemma linTilted_apply' {s : Set ℝ} (hs : MeasurableSet s) :
    μ.linTilted t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * a) / mgf id μ t) ∂μ := by
  rw [Measure.linTilted, tilted_apply' _ _ hs]
  rfl

lemma linTilted_apply [SFinite μ] (s : Set ℝ) :
    μ.linTilted t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * a) / mgf id μ t) ∂μ := by
  rw [Measure.linTilted, tilted_apply _ _]
  rfl

lemma linTilted_apply_cgf [IsProbabilityMeasure μ] (s : Set ℝ)
    (ht : Integrable (fun ω ↦ exp (t * ω)) μ) :
    μ.linTilted t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * a - cgf id μ t)) ∂μ := by
  simp_rw [linTilted_apply s, exp_sub]
  rw [exp_cgf]
  exact ht

lemma linTilted_apply_eq_ofReal_integral' {s : Set ℝ} (hs : MeasurableSet s) :
    μ.linTilted t s = ENNReal.ofReal (∫ a in s, exp (t * a) / mgf id μ t ∂μ) := by
  rw [Measure.linTilted, tilted_apply_eq_ofReal_integral' _ hs]
  rfl

lemma linTilted_apply_eq_ofReal_integral [SFinite μ] (s : Set ℝ) :
    μ.linTilted t s = ENNReal.ofReal (∫ a in s, exp (t * a) / mgf id μ t ∂μ) := by
  rw [Measure.linTilted, tilted_apply_eq_ofReal_integral _ s]
  rfl

lemma linTilted_apply_eq_ofReal_integral_cgf [IsProbabilityMeasure μ] (s : Set ℝ)
    (ht : Integrable (fun ω ↦ exp (t * ω)) μ) :
    μ.linTilted t s = ENNReal.ofReal (∫ a in s, exp (t * a - cgf id μ t) ∂μ) := by
  simp_rw [linTilted_apply_eq_ofReal_integral s, exp_sub]
  rw [exp_cgf]
  exact ht

end ProbabilityTheory
