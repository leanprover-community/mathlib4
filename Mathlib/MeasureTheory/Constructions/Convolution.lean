/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
/-!
# The convolution of measures

In this file we define and prove properties about the convolution of two measures

## Main definition

* `MeasureTheory.Measure.conv`: The convolution of two measures.

## Main results

* add
## Implementation Notes

## Tags

-/

noncomputable section

namespace MeasureTheory

namespace Measure

/-- Convolutions of measures. They are defined for arbitrary measures on a monoid M that is also
a measurable space. TODO: should get a to_additive version for AddMonoids -/
def conv {M : Type*} [Monoid M] [MeasurableSpace M] (μ : Measure M) (ν : Measure M) :
    Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (Measure.prod μ ν)

-- Convolution of the dirac measure at 1 with a measure μ returns μ. -/
theorem one_convolution {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : (Measure.dirac 1).conv μ = μ := by
  unfold conv
  rw [MeasureTheory.Measure.dirac_prod]
  rw [map_map]
  simp only [Function.comp_def, one_mul, map_id']
  all_goals { measurability }

/-- Convolution of a measure μ with the dirac measure at 1 returns μ. -/
theorem convolution_one {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ.conv (Measure.dirac 1) = μ := by
  unfold conv
  rw [MeasureTheory.Measure.prod_dirac, map_map]
  simp only [Function.comp_def, mul_one, map_id']
  all_goals { measurability }

/-- Convolution of the zero measure with a measure μ returns the zero measure. -/
theorem convolution_zero {M : Type*} [Monoid M] [MeasurableSpace M]
    (μ : Measure M) : (0 : Measure M).conv μ = (0 : Measure M) := by
  unfold conv
  simp

/-- Convolution of a measure μ with the zero measure returns the zero measure. -/
theorem zero_convolution {M : Type*} [Monoid M] [MeasurableSpace M]
    (μ : Measure M) : μ.conv (0 : Measure M) = (0 : Measure M) := by
  unfold conv
  simp

theorem convolution_add {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]
    (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ] [SFinite ν] [SFinite ρ]:
    μ.conv (ν + ρ) = μ.conv ν + μ.conv ρ := by
  unfold conv
  rw [prod_add, map_add]
  measurability

theorem add_convolution {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]
    (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ] [SFinite ν] [SFinite ρ]:
    (μ + ν).conv ρ = μ.conv ρ + ν.conv ρ := by
  unfold conv
  rw [add_prod, map_add]
  measurability

  /-- Convolution of SFinite maps is SFinite. -/
theorem sfinite_convolution_of_sfinite {M : Type*} [Monoid M] [MeasurableSpace M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : SFinite (μ.conv ν) :=
  instSFiniteMap (Measure.prod μ ν) fun x ↦ x.1 * x.2

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
theorem convolution_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
    (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] : μ.conv ν = ν.conv μ := by
  unfold conv
  rw [← prod_swap, map_map]
  · simp [Function.comp_def, mul_comm]
  all_goals { measurability }

theorem finite_of_finite_convolution {M : Type*} [Monoid M] [MeasurableSpace M] (μ : Measure M)
    (ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (μ.conv ν) := by
have h : (μ.conv ν) Set.univ < ⊤ := by
  unfold conv
  exact IsFiniteMeasure.measure_univ_lt_top
exact { measure_univ_lt_top := h}
