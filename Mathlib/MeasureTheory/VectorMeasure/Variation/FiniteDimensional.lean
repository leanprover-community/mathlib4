/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
/-!
# TODO

## Main results

TODO
-/

public section

open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X : Type*} {mX : MeasurableSpace X}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If a vector measure decomposes as a finite `ℝ`-linear combination `μ E = ∑ i, s i E • v i` of
signed measures `s i` with coefficients the vectors `v i`, then its variation is bounded by
`∑ i, ‖v i‖₊ • (s i).variation`. -/
lemma variation_le_sum_smul {ι : Type*} [Fintype ι] (μ : VectorMeasure X V)
    (s : ι → VectorMeasure X ℝ) (v : ι → V) (h : ∀ E, μ E = ∑ i, s i E • v i) :
    μ.variation ≤ ∑ i, ‖v i‖₊ • (s i).variation := by
  refine variation_le_of_forall_enorm_le fun E _ ↦ ?_
  calc ‖μ E‖ₑ = ‖∑ i, s i E • v i‖ₑ := by rw [h]
    _ ≤ ∑ i, ‖s i E • v i‖ₑ := enorm_sum_le _ _
    _ = ∑ i, ‖s i E‖ₑ * ‖v i‖ₑ := by simp_rw [enorm_smul]
    _ ≤ ∑ i, (s i).variation E * ‖v i‖ₑ := by
        gcongr with i _; exact enorm_measure_le_variation (s i) E
    _ = (∑ i, ‖v i‖₊ • (s i).variation) E := by
        rw [Measure.finsetSum_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Measure.coe_nnreal_smul_apply, mul_comm, enorm_eq_nnnorm]

end MeasureTheory.VectorMeasure
