/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Measure.PreVariation

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure` in an `ENormedAddCommMonoid`,
in particular, any `NormedAddCommGroup`.

Given a vector-valued measure `μ` we consider the problem of finding a countably additive function
`f` such that, for any set `E`, `‖μ(E)‖ ≤ f(E)`. This suggests defining `f(E)` as the supremum over
partitions `{Eᵢ}` of `E`, of the quantity `∑ᵢ, ‖μ(Eᵢ)‖`. Indeed any solution of the problem must be
not less than this function. It turns out that this function is a measure.

## Main definitions

* `VectorMeasure.ennrealVariation` — the variation as a `VectorMeasure X ℝ≥0∞`
* `VectorMeasure.variation` — the variation as a `Measure X`

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

variable {X : Type*} [MeasurableSpace X]

open MeasureTheory BigOperators NNReal ENNReal Function

namespace MeasureTheory.VectorMeasure

variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

/-- The norm of a vector measure is σ-subadditive on measurable sets. -/
lemma isSigmaSubadditiveSetFun_enorm (μ : VectorMeasure X V) :
    IsSigmaSubadditiveSetFun (‖μ ·‖ₑ) := by
  intro s hs
  have hmeas : ∀ i, MeasurableSet (s i).val := fun i => (s i).prop
  simpa [VectorMeasure.of_disjoint_iUnion hmeas hs] using enorm_tsum_le_tsum_enorm

/-- The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`. -/
noncomputable def ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ :=
  ennrealPreVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp)

/-- The variation of a `VectorMeasure` as a `Measure`. -/
noncomputable def variation (μ : VectorMeasure X V) : Measure X :=
  preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp)

end MeasureTheory.VectorMeasure
