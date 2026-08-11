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

* `variation_le_sum_smul`: if `μ` is a linear combination of `s i • v i`, then `μ.variation` can be
  bounded by ` ∑ i, ‖v i‖₊ • (s i).variation`.
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

variable {X : Type*} {mX : MeasurableSpace X}
  {V : Type*} [NormedAddCommGroup V]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V]

/-- If a vector measure decomposes as a finite linear combination `μ E = ∑ i, s i E • v i` of
signed measures `s i` with coefficients the vectors `v i`, then its variation is bounded by
`∑ i, ‖v i‖₊ • (s i).variation`. -/
lemma variation_le_sum_smul {ι : Type*} [Fintype ι] (μ : VectorMeasure X V)
    (s : ι → VectorMeasure X 𝕜) (v : ι → V) (h : ∀ E, μ E = ∑ i, s i E • v i) :
    μ.variation ≤ ∑ i, ‖v i‖₊ • (s i).variation := by
  refine variation_le_of_forall_enorm_le fun E _ ↦ ?_
  calc ‖μ E‖ₑ = ‖∑ i, s i E • v i‖ₑ := by rw [h]
    _ ≤ ∑ i, ‖s i E • v i‖ₑ := enorm_sum_le _ _
    _ = ∑ i, ‖v i‖ₑ * ‖s i E‖ₑ := by simp_rw [enorm_smul, mul_comm]
    _ ≤ ∑ i, ‖v i‖ₑ * (s i).variation E := by
        gcongr with i; exact enorm_measure_le_variation (s i) E
    _ = (∑ i, ‖v i‖₊ • (s i).variation) E := by simp [enorm_eq_nnnorm]

/-- The variation of a vector measure with values in a finite-dimensional real normed vector
space is finite. -/
instance [NormedSpace ℝ V] [FiniteDimensional ℝ V] (μ : VectorMeasure X V) :
    IsFiniteMeasure μ.variation := by
  obtain b := Module.finBasis ℝ V
  apply isFiniteMeasure_of_le (∑ i, ‖b i‖₊ • (μ.coeff b i).variation)
  apply variation_le_sum_smul
  simp

end MeasureTheory.VectorMeasure
