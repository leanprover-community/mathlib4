/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.MeasureTheory.Measure.Complex

/-!
# Properties of complex measures

We prove basic properties of `μ : ComplexMeasure α` on `MeasurableSpace X`.

## Main results

* `enorm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

noncomputable section

open MeasureTheory VectorMeasure

namespace MeasureTheory.ComplexMeasure

variable {α : Type*} [MeasurableSpace α]

/-- The real part of a complex measure as a complex measure. -/
def reCm : ComplexMeasure α →ₗ[ℝ] ComplexMeasure α where
  toFun := fun μ => μ.re.mapRangeₗ Complex.ofRealCLM.toLinearMap Complex.ofRealCLM.continuous
  map_add' := by intro; simp
  map_smul' := by intro; simp

@[simp]
lemma reCm_apply (μ : ComplexMeasure α) (E : Set α) : μ.reCm E = μ.re E := by simp [reCm]

lemma variation_reCm_eq_variation_re (μ : ComplexMeasure α) :
    μ.reCm.variation = μ.re.variation := by sorry
  -- apply variation_eq_of_forall_enorm_eq

/-- The imaginary part of a complex measure as a complex measure. -/
def imCm : ComplexMeasure α →ₗ[ℝ] ComplexMeasure α where
  toFun := fun μ => μ.im.mapRangeₗ Complex.ofRealCLM.toLinearMap Complex.ofRealCLM.continuous
  map_add' := by intro; simp
  map_smul' := by intro; simp

@[simp]
lemma imCm_apply (μ : ComplexMeasure α) (E : Set α) : μ.imCm E = μ.im E := by simp [imCm]

lemma variation_imCm_eq_variation_im (μ : ComplexMeasure α) :
    μ.imCm.variation = μ.im.variation := by sorry
  -- apply variation_eq_of_forall_enorm_eq

lemma eq_add_re_im (μ : ComplexMeasure α) : μ = μ.reCm + Complex.I • μ.imCm := by
  ext E; apply Complex.ext <;> simp

theorem isFiniteMeasure (μ : ComplexMeasure α) : IsFiniteMeasure μ.variation := by
  rw [μ.eq_add_re_im, isFiniteMeasure_iff]
  apply lt_of_le_of_lt (by apply variation_add_le _ _)
  rw [Measure.add_apply, ENNReal.add_lt_top]
  constructor
  · rw [variation_reCm_eq_variation_re]
    sorry
    -- re.variation = re.totalVariation, use finiteness
  · sorry
    -- similar

end MeasureTheory.ComplexMeasure
