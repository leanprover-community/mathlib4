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

open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X : Type*} {mX : MeasurableSpace X} {V : Type*} [NormedAddCommGroup V]

/-- The variation of a vector measure with values in a real finite-dimensional normed vector space
is finite. -/
instance [NormedSpace ℝ V] [FiniteDimensional ℝ V] (μ : VectorMeasure X V) :
    IsFiniteMeasure μ.variation := by
  let b := (Module.finBasis ℝ V).toGeneralSchauderBasis
  exact isFiniteMeasure_of_le (∑ i, ‖b i‖₊ • (μ.coord b i).variation)
    (variation_le_sum_smul (by simp))

end MeasureTheory.VectorMeasure
