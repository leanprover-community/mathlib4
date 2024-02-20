/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
import Mathlib.Topology.GPseudoMetricSpace.Basic

/-!
# General Metric Spaces

this file defines General Metric Spaces, which are a generalisation of Metric Spaces and Extended
metric spaces. In this case, the codomain can be any linearly ordered (additive) commutative monoid,
rather than only ℝ or ℝ≥0∞.

## Main Definitions

- `GMetricSpace α β`: a space endowed with a distance function with codomain `β`, which returns 0
iff the arguments are equal.

## Implementation Notes

A lot of elementary properties don't require `eq_of_gdist_eq_zero`, hence are stated and proven
for `GPseudoMetricSpace`s in `GPseudoMetric/Basic.lean`.
-/

/-- We now define `GMetricSpace`, extending `GPseudoMetricSpace`. -/
class GMetricSpace (α : Type*) (β : Type*) [LinearOrder β] [AddCommMonoid β]
    [IsOrderedAddCommMonoid β] extends GPseudoMetricSpace α β where
  eq_of_dist_eq_zero : ∀ {x y : α}, gdist x y = 0 → x = y

variable {α:Type*} {β:Type*} [LinearOrder β] [AddCommMonoid β]
    [IsOrderedAddCommMonoid β]

/-- Two generalised metric space structures with the same distance coincide. -/
@[ext]
theorem GMetricSpace.ext {m m' : GMetricSpace α β} (h : m.toGDist = m'.toGDist) :
    m = m' := by
  cases m; cases m'; congr; ext1; assumption
