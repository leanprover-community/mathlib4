/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!

# Vector-valued measures

This file defines vector-valued measures, which are σ-additive functions from a set to an
additive monoid `M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `SignedMeasure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `ComplexMeasure α`
(defined in `MeasureTheory/Measure/Complex`).

## Main definitions

* `MeasureTheory.VectorMeasure` is a vector-valued, σ-additive function that maps the empty
  and non-measurable sets to zero.
* `MeasureTheory.SignedMeasure` is a real-valued vector measure.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `HasSum` instead of `tsum` in the definition of vector measures in comparison to `Measure`
since this provides summability.

## Tags

vector measure, signed measure, complex measure
-/

public section

open scoped Function -- required for scoped `on` notation
namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α}

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
an additive monoid) such that the empty set and non-measurable sets are mapped to zero. -/
structure VectorMeasure (α : Type*) [MeasurableSpace α] (M : Type*) [AddCommMonoid M]
    [TopologicalSpace M] where
  /-- The measure of sets -/
  measureOf' : Set α → M
  /-- The empty set has measure zero -/
  empty' : measureOf' ∅ = 0
  /-- Non-measurable sets have measure zero -/
  not_measurable' ⦃i : Set α⦄ : ¬MeasurableSet i → measureOf' i = 0
  /-- The measure is σ-additive -/
  m_iUnion' ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    HasSum (fun i => measureOf' (f i)) (measureOf' (⋃ i, f i))

/-- A `SignedMeasure` is an `ℝ`-vector measure. -/
abbrev SignedMeasure (α : Type*) [MeasurableSpace α] :=
  VectorMeasure α ℝ

namespace VectorMeasure

section

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

instance : FunLike (VectorMeasure α M) (Set α) M where
  coe := VectorMeasure.measureOf'
  coe_injective v w h := by
    cases v; cases w; congr

@[simp]
theorem coe_mk (v : Set α → M) (h₁) (h₂) (h₃) : (mk v h₁ h₂ h₃ : VectorMeasure α M) = v := rfl

initialize_simps_projections VectorMeasure (measureOf' → apply)

end

end VectorMeasure

end MeasureTheory
