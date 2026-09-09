/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Frostman's mass distribution principle

If a measure `ν` on a metric space `X` gives each set `s` of diameter `≤ ε` a
mass bounded by `ν s ≤ ediam s ^ d`, and `ν A ≠ 0`, then `d ≤ dimH A` (the
Hausdorff dimension of `A` is at least `d`).

This is the **mass distribution principle** (a.k.a. Frostman's lemma, easy
direction), the standard lower bound on Hausdorff dimension. It packages two
existing Mathlib lemmas — `Measure.le_hausdorffMeasure` (the measure bound
`ν ≤ μH[d]`) and `le_dimH_of_hausdorffMeasure_ne_zero` (`μH[d] A ≠ 0 ⇒ d ≤
dimH A`) — into the single statement that appears in every textbook on
fractal geometry.

## Main results

* `massBound_le_dimH`: if `ν s ≤ ediam s ^ d` for small sets and `ν A ≠ 0`,
  then `d ≤ dimH A`.

## References

* K. Falconer, *Fractal Geometry* (Wiley, 3rd ed., 2014), §4.1.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces* (Cambridge,
  1995), §4.9.

## Tags

Hausdorff dimension, Frostman, mass distribution principle, fractal
-/

open scoped MeasureTheory ENNReal NNReal

namespace MeasureTheory

/-- **Frostman's mass distribution principle.** If `ν s ≤ ediam s ^ d` for all
sets `s` of diameter `≤ ε`, and `ν A ≠ 0`, then `d ≤ dimH A`. -/
theorem massBound_le_dimH
    (ν : Measure X) (A : Set X) (d : ℝ≥0)
    (hνA : ν A ≠ 0)
    (ε : ℝ≥0∞) (hε : 0 < ε)
    (hbound : ∀ s : Set X, Metric.ediam s ≤ ε → ν s ≤ Metric.ediam s ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimH A := by
  -- Mass distribution: `ν ≤ μH[d]`.
  have hle : ν ≤ μH[(d : ℝ)] := le_hausdorffMeasure (d : ℝ) ν ε hε hbound
  -- In particular `ν A ≤ μH[d] A`, so `μH[d] A ≠ 0`.
  have hνle : ν A ≤ μH[(d : ℝ)] A := le_iff'.mp hle A
  have hAne : μH[(d : ℝ)] A ≠ 0 := by
    intro h0
    exact hνA (le_antisymm (h0 ▸ hνle) zero_le)
  -- `μH[d] A ≠ 0 ⇒ d ≤ dimH A`.
  exact le_dimH_of_hausdorffMeasure_ne_zero hAne

end MeasureTheory
