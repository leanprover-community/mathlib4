/-
Copyright (c) 2025 Loic Simon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loic Simon
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Jordan decomposition from signed measure subtraction

This file develops the Jordan decomposition of the signed measure `μ - ν` for finite measures `μ`
and `ν`, expressing it as the pair `(μ - ν, ν - μ)` of mutually singular finite measures.

The key tool is the Hahn decomposition theorem, which yields a measurable partition of the space
where `μ ≤ ν` and `ν ≤ μ`, and the measure difference behaves like a signed measure difference.

## Main results

* `toJordanDecomposition_toSignedMeasure_sub`:
  The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is given by
  `(μ - ν, ν - μ)`. It relies on the following intermediate results.
* `mutually_singular_measure_sub`:
  The measures `μ - ν` and `ν - μ` are mutually singular.
* `sub_toSignedMeasure_eq_toSignedMeasure_sub`:
  The signed measure `μ.toSignedMeasure - ν.toSignedMeasure` equals
  `(μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory.Measure

noncomputable section

variable {X : Type*} {mX : MeasurableSpace X}
variable {s : Set X}
variable {μ ν : Measure X}

lemma sub_apply_eq_zero_of_isHahnDecomposition
    (hs : IsHahnDecomposition μ ν s) : (μ - ν) s = 0 := by
  rw [← restrict_eq_zero, restrict_sub_eq_restrict_sub_restrict hs.measurableSet]
  exact sub_eq_zero_of_le hs.le_on

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem mutually_singular_measure_sub :
    (μ - ν).MutuallySingular (ν - μ) := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  exact ⟨s, hs.measurableSet,
    sub_apply_eq_zero_of_isHahnDecomposition hs,
    sub_apply_eq_zero_of_isHahnDecomposition hs.compl⟩

lemma toSignedMeasure_restrict_sub (hs : IsHahnDecomposition μ ν s) :
    ((ν - μ).restrict s).toSignedMeasure =
      ν.toSignedMeasure.restrict s - μ.toSignedMeasure.restrict s := by
  have hmeas := hs.measurableSet
  rw [eq_sub_iff_add_eq, toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hmeas,
    ← toSignedMeasure_add]
  simp only [restrict_sub_eq_restrict_sub_restrict, hmeas, sub_add_cancel_of_le hs.le_on]
  exact (toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hmeas).symm

theorem sub_toSignedMeasure_eq_toSignedMeasure_sub :
    μ.toSignedMeasure - ν.toSignedMeasure =
      (μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hsc := hs.compl
  have h₁ := toSignedMeasure_restrict_sub hs
  have h₂ := toSignedMeasure_restrict_sub hsc
  have h₁' := toSignedMeasure_congr <| restrict_eq_zero.mpr <|
    sub_apply_eq_zero_of_isHahnDecomposition hs
  have h₂' := toSignedMeasure_congr <| restrict_eq_zero.mpr <|
  sub_apply_eq_zero_of_isHahnDecomposition hsc
  have partition₁ := VectorMeasure.restrict_add_restrict_compl (μ - ν).toSignedMeasure
    hs.measurableSet
  have partition₂ := VectorMeasure.restrict_add_restrict_compl (ν - μ).toSignedMeasure
    hs.measurableSet
  rw [toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hs.measurableSet,
    toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hs.measurableSet.compl]
    at partition₁ partition₂
  rw [h₁', h₂] at partition₁
  rw [h₁, h₂'] at partition₂
  simp only [toSignedMeasure_zero, zero_add] at partition₁ partition₂
  rw [← VectorMeasure.restrict_add_restrict_compl μ.toSignedMeasure hs.measurableSet,
    ← VectorMeasure.restrict_add_restrict_compl ν.toSignedMeasure hs.measurableSet,
    ← partition₁, ← partition₂]
  repeat rw [sub_eq_add_neg]
  abel

/-- The Jordan decomposition associated to the pair of mutually singular measures `μ - ν`
and `ν - μ`. -/
def jordanDecompositionOfToSignedMeasureSub
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : JordanDecomposition X where
  posPart := μ - ν
  negPart := ν - μ
  mutuallySingular := mutually_singular_measure_sub

lemma jordanDecompositionOfToSignedMeasureSub_posPart :
    (jordanDecompositionOfToSignedMeasureSub μ ν).posPart = μ - ν := rfl

lemma jordanDecompositionOfToSignedMeasureSub_negPart :
    (jordanDecompositionOfToSignedMeasureSub μ ν).negPart = ν - μ := rfl

lemma jordanDecompositionOfToSignedMeasureSub_toSignedMeasure :
    (jordanDecompositionOfToSignedMeasureSub μ ν).toSignedMeasure =
    μ.toSignedMeasure - ν.toSignedMeasure := by
  simp_rw [JordanDecomposition.toSignedMeasure, jordanDecompositionOfToSignedMeasureSub_posPart,
    jordanDecompositionOfToSignedMeasureSub_negPart, ← sub_toSignedMeasure_eq_toSignedMeasure_sub]

/-- The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is `(μ - ν, ν - μ)`. -/
@[simp]
theorem toJordanDecomposition_toSignedMeasure_sub :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition =
      jordanDecompositionOfToSignedMeasureSub μ ν := by
  apply JordanDecomposition.toSignedMeasure_injective
  rw [SignedMeasure.toSignedMeasure_toJordanDecomposition,
    jordanDecompositionOfToSignedMeasureSub_toSignedMeasure]

end

end MeasureTheory.Measure
