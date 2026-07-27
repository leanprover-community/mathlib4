/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Properties of complex measures

We prove basic properties of `μ : ComplexMeasure X` on `MeasurableSpace X`.

## Main definitions and results

* `reCm`, `imCm` : the real and imaginary parts of a complex measure as complex measures.
* `eq_add_re_im` : a complex measure is the sum of its real and imaginary parts.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

noncomputable section

open MeasureTheory VectorMeasure

namespace MeasureTheory.ComplexMeasure

variable {X : Type*} {mX : MeasurableSpace X}

/-- The real part of a complex measure as a complex measure. -/
def reCm : ComplexMeasure X →ₗ[ℝ] ComplexMeasure X where
  toFun := fun μ => μ.re.mapRangeₗ Complex.ofRealCLM.toLinearMap Complex.ofRealCLM.continuous
  map_add' := by intro; simp [_root_.map_add]
  map_smul' := by intro; simp

@[simp]
lemma reCm_apply (μ : ComplexMeasure X) (E : Set X) : μ.reCm E = μ.re E := by simp [reCm]

lemma variation_reCm_eq_variation_re (μ : ComplexMeasure X) :
    μ.reCm.variation = μ.re.variation := by
  apply variation_eq_of_forall_enorm_eq; intro _ _; simp [← ofReal_norm]

/-- The imaginary part of a complex measure as a complex measure. -/
def imCm : ComplexMeasure X →ₗ[ℝ] ComplexMeasure X where
  toFun := fun μ => μ.im.mapRangeₗ Complex.ofRealCLM.toLinearMap Complex.ofRealCLM.continuous
  map_add' := by intro; simp [_root_.map_add]
  map_smul' := by intro; simp

@[simp]
lemma imCm_apply (μ : ComplexMeasure X) (E : Set X) : μ.imCm E = μ.im E := by simp [imCm]

lemma variation_imCm_eq_variation_im (μ : ComplexMeasure X) :
    μ.imCm.variation = μ.im.variation := by
  apply variation_eq_of_forall_enorm_eq; intro _ _; simp [← ofReal_norm]

theorem eq_add_re_im (μ : ComplexMeasure X) : μ = μ.reCm + Complex.I • μ.imCm := by
  ext E; apply Complex.ext <;> simp <;> rfl

end MeasureTheory.ComplexMeasure
