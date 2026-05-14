/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Measure.PreVariation
public import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure` in an `ENormedAddCommMonoid`,
in particular, any `NormedAddCommGroup`.

Given a vector-valued measure `μ` we consider the problem of finding a countably additive function
`f` such that, for any set `E`, `‖μ(E)‖ ≤ f(E)`. This suggests defining `f(E)` as the supremum over
partitions `{Eᵢ}` of `E`, of the quantity `∑ᵢ, ‖μ(Eᵢ)‖`. Indeed any solution of the problem must be
not less than this function. It turns out that this function is a measure.

## Main definitions

* `VectorMeasure.variation`: the variation as a `Measure X`
* `VectorMeasure.ennrealVariation`: the variation as a `VectorMeasure X ℝ≥0∞`

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

variable {X : Type*} [MeasurableSpace X]

open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

/-- The norm of a vector measure is σ-subadditive on measurable sets. -/
lemma isSigmaSubadditiveSetFun_enorm (μ : VectorMeasure X V) :
    IsSigmaSubadditiveSetFun (‖μ ·‖ₑ) := by
  intro s hs
  have hmeas : ∀ i, MeasurableSet (s i).val := fun i => (s i).prop
  simpa [VectorMeasure.of_disjoint_iUnion hmeas hs] using enorm_tsum_le_tsum_enorm

/-- The variation of a `VectorMeasure` as a `Measure`. -/
noncomputable def variation (μ : VectorMeasure X V) : Measure X :=
  preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp)

/-- The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`. -/
noncomputable def ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ :=
  μ.variation.toENNRealVectorMeasure

end MeasureTheory.VectorMeasure
