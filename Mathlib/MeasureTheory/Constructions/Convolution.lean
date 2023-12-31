/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
/-!
# The product measure

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

theorem finite_of_finite_conv {M : Type*} [Monoid M] [MeasurableSpace M] (μ : Measure M)
    (ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (μ.conv ν) := by
  have h : (μ.conv ν) Set.univ < ⊤ := by
    unfold conv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact { measure_univ_lt_top := h}

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
theorem comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
    (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] : μ.conv ν = ν.conv μ := by
  unfold conv
  rw [← prod_swap, map_map]
  · simp [Function.comp_def, mul_comm]
  all_goals { measurability }
