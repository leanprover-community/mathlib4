/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# The multiplicative and additive convolution of measures

In this file we define and prove properties about the convolutions of two measures.

## Main definitions

* `MeasureTheory.Measure.mconv`: The multiplicative convolution of two measures: the map of `*`
  under the product measure.
* `MeasureTheory.Measure.conv`: The additive convolution of two measures: the map of `+`
  under the product measure.
-/

namespace MeasureTheory

namespace Measure

variable {M : Type*} [Monoid M] [MeasurableSpace M]

/-- Multiplicative convolution of measures. -/
@[to_additive conv "Additive convolution of measures."]
noncomputable def mconv (μ : Measure M) (ν : Measure M) :
    Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)

/-- Scoped notation for the multiplicative convolution of measures. -/
scoped[MeasureTheory] infix:80 " ∗ " => MeasureTheory.Measure.mconv

/-- Scoped notation for the additive convolution of measures. -/
scoped[MeasureTheory] infix:80 " ∗ " => MeasureTheory.Measure.conv

/-- Convolution of the dirac measure at 1 with a measure μ returns μ. -/
@[to_additive (attr := simp)]
theorem dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (Measure.dirac 1) ∗ μ = μ := by
  unfold mconv
  rw [MeasureTheory.Measure.dirac_prod, map_map]
  · simp only [Function.comp_def, one_mul, map_id']
  all_goals { measurability }

/-- Convolution of a measure μ with the dirac measure at 1 returns μ. -/
@[to_additive (attr := simp)]
theorem mconv_dirac_one [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ ∗ (Measure.dirac 1) = μ := by
  unfold mconv
  rw [MeasureTheory.Measure.prod_dirac, map_map]
  · simp only [Function.comp_def, mul_one, map_id']
  all_goals { measurability }

/-- Convolution of the zero measure with a measure μ returns the zero measure. -/
@[to_additive (attr := simp) conv_zero]
theorem mconv_zero (μ : Measure M) : (0 : Measure M) ∗ μ = (0 : Measure M) := by
  unfold mconv
  simp

/-- Convolution of a measure μ with the zero measure returns the zero measure. -/
@[to_additive (attr := simp) zero_conv]
theorem zero_mconv (μ : Measure M) : μ ∗ (0 : Measure M) = (0 : Measure M) := by
  unfold mconv
  simp

@[to_additive conv_add]
theorem mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : μ ∗ (ν + ρ) = μ ∗ ν + μ ∗ ρ := by
  unfold mconv
  rw [prod_add, map_add]
  measurability

@[to_additive add_conv]
theorem add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : (μ + ν) ∗ ρ = μ ∗ ρ + ν ∗ ρ := by
  unfold mconv
  rw [add_prod, map_add]
  measurability

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
@[to_additive conv_comm]
theorem mconv_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ ν = ν ∗ μ := by
  unfold mconv
  rw [← prod_swap, map_map]
  · simp [Function.comp_def, mul_comm]
  all_goals { measurability }

/-- Convolution of SFinite maps is SFinite. -/
@[to_additive sfinite_conv_of_sfinite]
instance sfinite_mconv_of_sfinite (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] :
    SFinite (μ ∗ ν) := inferInstanceAs <| SFinite ((μ.prod ν).map fun (x : M × M) ↦ x.1 * x.2)

@[to_additive finite_of_finite_conv]
instance finite_of_finite_mconv (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ ν) := by
  have h : (μ ∗ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact {measure_univ_lt_top := h}

@[to_additive probabilitymeasure_of_probabilitymeasures_conv]
instance probabilitymeasure_of_probabilitymeasures_mconv (μ : Measure M) (ν : Measure M)
    [MeasurableMul₂ M] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ ∗ ν) := by
  apply MeasureTheory.isProbabilityMeasure_map
  measurability

end Measure

end MeasureTheory
