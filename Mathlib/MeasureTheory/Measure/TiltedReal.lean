/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Measure tilted by a real number

This is a particular case of `Measure.tilted` where the tilting function is multiplication of a
real random variable by a real number: `μ.tiltedReal X t = μ.tilted (fun ω ↦ t * X ω)`.

## Main definitions

* `MeasureTheory.Measure.tiltedReal X μ t`: the measure `μ.tilted (fun ω ↦ t * X ω)`.

## Main statements

* `fooBar_unique`

## Implementation details

TODO: explain (X, μ) vs μ. (μ.map X, (id, μ))

-/

open MeasureTheory Real Set Finset

open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {X : Ω → ℝ} {t u : ℝ}

namespace MeasureTheory

/-- Exponentially tilted measure. When `ω ↦ exp (t * X ω)` is integrable, `μ.tiltedReal X t` is the
probability measure with density with respect to `μ` proportional to `exp (t * X)`.
Otherwise it is 0.
-/
noncomputable
def Measure.tiltedReal (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : Measure Ω := μ.tilted (fun ω ↦ t * X ω)

instance : IsZeroOrProbabilityMeasure (μ.tiltedReal X t) := by
  rw [Measure.tiltedReal]; infer_instance

@[simp]
lemma tiltedReal_zero_measure : (0 : Measure Ω).tiltedReal X t = 0 := by simp [Measure.tiltedReal]

@[simp]
lemma tiltedReal_zero' : μ.tiltedReal X (0 : ℝ) = (μ univ)⁻¹ • μ := by simp [Measure.tiltedReal]

lemma tiltedReal_zero [IsZeroOrProbabilityMeasure μ] : μ.tiltedReal X (0 : ℝ) = μ := by simp

lemma isProbabilityMeasure_tiltedReal [NeZero μ] (hf : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    IsProbabilityMeasure (μ.tiltedReal X t) :=
  isProbabilityMeasure_tilted hf

instance isZeroOrProbabilityMeasure_tiltedReal : IsZeroOrProbabilityMeasure (μ.tiltedReal X t) :=
  isZeroOrProbabilityMeasure_tilted

lemma tiltedReal_absolutelyContinuous (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : μ.tiltedReal X t ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma tiltedReal_apply' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tiltedReal X t s
      = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / ∫ ω, exp (t * X ω) ∂μ) ∂μ := by
  rw [Measure.tiltedReal, tilted_apply' _ _ hs]

lemma tiltedReal_apply [SFinite μ] (s : Set Ω) :
    μ.tiltedReal X t s
      = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / ∫ ω, exp (t * X ω) ∂μ) ∂μ := by
  rw [Measure.tiltedReal, tilted_apply _ _]

lemma tiltedReal_apply_eq_ofReal_integral' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tiltedReal X t s
      = ENNReal.ofReal (∫ a in s, exp (t * X a) / ∫ ω, exp (t * X ω) ∂μ ∂μ) := by
  rw [Measure.tiltedReal, tilted_apply_eq_ofReal_integral' _ hs]

lemma tiltedReal_apply_eq_ofReal_integral [SFinite μ] (s : Set Ω) :
    μ.tiltedReal X t s
      = ENNReal.ofReal (∫ a in s, exp (t * X a) / ∫ ω, exp (t * X ω) ∂μ ∂μ) := by
  rw [Measure.tiltedReal, tilted_apply_eq_ofReal_integral _ s]

lemma tiltedReal_id_map (hX : Measurable X) :
    (μ.map X).tiltedReal id t = (μ.tiltedReal X t).map X := by
  ext s hs
  rw [tiltedReal_apply' hs, Measure.map_apply hX hs, tiltedReal_apply',
    setLIntegral_map (μ := μ) hs _ hX]
  · simp only [id_eq]
    congr with ω
    congr
    rw [integral_map hX.aemeasurable]
    exact AEMeasurable.aestronglyMeasurable <| by fun_prop
  · fun_prop
  · exact hX hs

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integrable_tiltedReal_iff (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) (g : Ω → E) :
    Integrable g (μ.tiltedReal X t) ↔ Integrable (fun ω ↦ exp (t * X ω) • g ω) μ := by
  rw [Measure.tiltedReal, integrable_tilted_iff ht]

/-- For a version that does not assume that the set is measurable, but works only for s-finite
measures, see `setIntegral_tiltedReal`. -/
lemma setIntegral_tiltedReal' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tiltedReal X t)
      = ∫ x in s, (exp (t * X x) / ∫ ω, exp (t * X ω) ∂μ) • (g x) ∂μ := by
  rw [Measure.tiltedReal, setIntegral_tilted' _ _ hs]

lemma setIntegral_tiltedReal [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.tiltedReal X t)
      = ∫ x in s, (exp (t * X x) / ∫ ω, exp (t * X ω) ∂μ) • (g x) ∂μ := by
  rw [Measure.tiltedReal, setIntegral_tilted]

lemma integral_tiltedReal (g : Ω → E) :
    ∫ ω, g ω ∂(μ.tiltedReal X t) = ∫ ω, (exp (t * X ω) / ∫ ω, exp (t * X ω) ∂μ) • (g ω) ∂μ := by
  rw [Measure.tiltedReal, integral_tilted]

end Integral
end MeasureTheory
