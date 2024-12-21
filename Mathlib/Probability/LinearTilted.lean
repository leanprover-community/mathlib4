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

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}

/-- Exponentially tilted measure. When `x ↦ exp (t * x)` is integrable, `μ.linTilted t` is the
probability measure with density with respect to `μ` proportional to `exp (t * x)`.
Otherwise it is 0.
-/
noncomputable
def _root_.MeasureTheory.Measure.linTilted (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : Measure Ω :=
  μ.tilted (fun ω ↦ t * X ω)

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

instance : IsZeroOrProbabilityMeasure (μ.linTilted X t) := by
  rw [Measure.linTilted]; infer_instance

@[simp]
lemma linTilted_zero_measure : (0 : Measure Ω).linTilted X t = 0 := by simp [Measure.linTilted]

@[simp]
lemma linTilted_zero' : μ.linTilted X (0 : ℝ) = (μ Set.univ)⁻¹ • μ := by simp [Measure.linTilted]

@[simp]
lemma linTilted_zero [IsZeroOrProbabilityMeasure μ] : μ.linTilted X (0 : ℝ) = μ := by
  rw [linTilted_zero']
  cases eq_zero_or_isProbabilityMeasure μ with
  | inl h => simp [h]
  | inr h => simp [h]

lemma linTilted_apply' {s : Set Ω} (hs : MeasurableSet s) :
    μ.linTilted X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [Measure.linTilted, tilted_apply' _ _ hs]
  rfl

lemma linTilted_apply [SFinite μ] (s : Set Ω) :
    μ.linTilted X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [Measure.linTilted, tilted_apply _ _]
  rfl

lemma linTilted_apply_cgf [IsProbabilityMeasure μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.linTilted X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  simp_rw [linTilted_apply s, exp_sub]
  rw [exp_cgf]
  exact ht

lemma linTilted_apply_eq_ofReal_integral' {s : Set Ω} (hs : MeasurableSet s) :
    μ.linTilted X t s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [Measure.linTilted, tilted_apply_eq_ofReal_integral' _ hs]
  rfl

lemma linTilted_apply_eq_ofReal_integral [SFinite μ] (s : Set Ω) :
    μ.linTilted X t s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [Measure.linTilted, tilted_apply_eq_ofReal_integral _ s]
  rfl

lemma linTilted_apply_eq_ofReal_integral_cgf [IsProbabilityMeasure μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.linTilted X t s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  simp_rw [linTilted_apply_eq_ofReal_integral s, exp_sub]
  rw [exp_cgf]
  exact ht

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a version that does not assume that the set is measurable, but works only for s-finite
measures, see `setIntegral_linTilted`. -/
lemma setIntegral_linTilted' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.linTilted X t) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [Measure.linTilted, setIntegral_tilted' _ _ hs, mgf]

lemma setIntegral_linTilted [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.linTilted X t) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [Measure.linTilted, setIntegral_tilted, mgf]

lemma integral_linTilted (g : Ω → E) :
    ∫ ω, g ω ∂(μ.linTilted X t) = ∫ ω, (exp (t * X ω) / mgf X μ t) • (g ω) ∂μ := by
  rw [Measure.linTilted, integral_tilted, mgf]

lemma integral_linTilted_self [IsFiniteMeasure μ]
    (ht : t ∈ interior {x | Integrable (fun ω ↦ rexp (x * X ω)) μ}):
    (μ.linTilted X t)[X] = deriv (cgf X μ) t := by
  rw [integral_linTilted, deriv_cgf ht, ← integral_div, mgf]
  congr with ω
  rw [smul_eq_mul]
  ring

end Integral

end ProbabilityTheory
