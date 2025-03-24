/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Order.Real

/-!
# Definitions of an outer measure and the corresponding `FunLike` class

In this file we define `MeasureTheory.OuterMeasure α`
to be the type of outer measures on `α`.

An outer measure is a function `μ : Set α → ℝ≥0∞`,
from the powerset of a type to the extended nonnegative real numbers
that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union
   is at most the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

We also define a typeclass `MeasureTheory.OuterMeasureClass`.

## References

<https://en.wikipedia.org/wiki/Outer_measure>

## Tags

outer measure
-/

assert_not_exists Basis IsTopologicalRing UniformSpace

open scoped ENNReal

variable {α : Type*}

namespace MeasureTheory

open scoped Function -- required for scoped `on` notation

/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure OuterMeasure (α : Type*) where
  /-- Outer measure function. Use automatic coercion instead. -/
  protected measureOf : Set α → ℝ≥0∞
  protected empty : measureOf ∅ = 0
  protected mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  protected iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
    measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)

/-- A mixin class saying that elements `μ : F` are outer measures on `α`.

This typeclass is used to unify some API for outer measures and measures. -/
class OuterMeasureClass (F : Type*) (α : outParam Type*) [FunLike F (Set α) ℝ≥0∞] : Prop where
  protected measure_empty (f : F) : f ∅ = 0
  protected measure_mono (f : F) {s t} : s ⊆ t → f s ≤ f t
  protected measure_iUnion_nat_le (f : F) (s : ℕ → Set α) : Pairwise (Disjoint on s) →
    f (⋃ i, s i) ≤ ∑' i, f (s i)

namespace OuterMeasure

instance : FunLike (OuterMeasure α) (Set α) ℝ≥0∞ where
  coe m := m.measureOf
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

@[simp] theorem measureOf_eq_coe (m : OuterMeasure α) : m.measureOf = m := rfl

instance : OuterMeasureClass (OuterMeasure α) α where
  measure_empty f := f.empty
  measure_mono f := f.mono
  measure_iUnion_nat_le f := f.iUnion_nat

end OuterMeasure

end MeasureTheory
