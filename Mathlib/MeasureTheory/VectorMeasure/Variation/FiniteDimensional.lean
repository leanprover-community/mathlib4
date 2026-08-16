/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

import Mathlib.MeasureTheory.VectorMeasure.FiniteDimensional
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Finiteness of the variation of a vector measure in a finite-dimensional vector space

## Main results

* instance `IsFiniteMeasure μ.variation` for any vector measure `μ` in a finite-dimensional
  `ℝ`-vector space `V`.

## Note

The finite-dimensionality of `ℂ` over `ℝ` is given in
`Mathlib.LinearAlgebra.Complex.FiniteDimensional`. When one needs `IsFiniteMeasure μ.variation` for
`μ : ComplexMeasure V`, one should import that and this file.

-/

public section

namespace MeasureTheory.VectorMeasure

variable {X : Type*} {mX : MeasurableSpace X} {V : Type*} [NormedAddCommGroup V]

/-- The variation of a vector measure with values in a real finite-dimensional normed vector space
is finite. -/
instance [NormedSpace ℝ V] [FiniteDimensional ℝ V] (μ : VectorMeasure X V) :
    IsFiniteMeasure μ.variation := by
  let b := (Module.finBasis ℝ V).toUnconditionalSchauderBasis
  apply isFiniteMeasure_of_le (∑ i, ‖b i‖₊ • (μ.coord b i).variation)
  nth_rw 1 [sum_toSpanSingleton_coord_eq b μ]
  apply le_trans (variation_finsetSum_le _ _)
  gcongr
  refine variation_le_of_forall_enorm_le fun E _ ↦ ?_
  simp only [mapRangeₗ_apply, coord_apply, LinearMap.toSpanSingleton_apply, Measure.smul_apply,
    Measure.nnreal_smul_coe_apply]
  calc
    ‖(b.coord i) (μ E) • b i‖ₑ ≤ ‖b i‖ₑ * ‖(b.coord i) (μ E)‖ₑ := by
        rw [mul_comm]
        exact enorm_smul_le
    _ ≤ ‖b i‖₊ * ‖VectorMeasure.coord b μ i E‖ₑ := by
        gcongr <;> simp
    _ ≤ ‖b i‖₊ * (VectorMeasure.coord b μ i).variation E := by
        gcongr; exact enorm_measure_le_variation _ _

end MeasureTheory.VectorMeasure
