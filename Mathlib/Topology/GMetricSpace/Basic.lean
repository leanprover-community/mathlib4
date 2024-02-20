/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
import Mathlib.Topology.GPseudoMetric.Basic

/-!
# General Metric Spaces

this file defines Generic Metrics, which are a generalisation of Metrics and Extended
Metrics. In this case, the codomain can be any linearly ordered (additive) commutative monoid,
rather than only ℝ or ℝ≥0∞.

## Main Definitions

- `GMetric α β`: a distance function on `α` with codomain `β`, which returns 0
iff the arguments are equal.

## Implementation Notes

A lot of elementary properties don't require `eq_of_gdist_eq_zero`, hence are stated and proven
for `GPseudoMetric`s in `GPseudoMetric/Basic.lean`.
-/

/-- We now define `GMetric`, extending `GPseudoMetric`. -/
structure GMetric (α : Type*) (β : Type*) [LinearOrder β] [AddCommMonoid β]
    [IsOrderedAddCommMonoid β] extends GPseudoMetric α β where
  eq_of_dist_eq_zero : ∀ {x y : α}, toFun x y = 0 → x = y

variable {α:Type*} {β:Type*} [LinearOrder β] [AddCommMonoid β]
    [IsOrderedAddCommMonoid β]

/-- Two generalised metrics with the same distance function coincide. -/
@[ext]
theorem GMetric.ext {gdist₁ gdist₂ : GMetric α β} (h : gdist₁.toFun = gdist₂.toFun) :
    gdist₁ = gdist₂ := by
  cases gdist₁; cases gdist₂; congr; ext1; assumption

/-- the class of types that are generalised metrics on α to β-/
class GMetricClass
    (T:Type*) (α β :outParam Type*) [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β]
    [FunLike T α (α → β)] extends GPseudoMetricClass T α β : Prop where
  eq_of_dist_eq_zero : ∀ (gdist:T), ∀ {x y : α}, gdist x y = 0 → x = y

instance GMetric.instFunLike: FunLike (GMetric α β) α (α → β) where
  coe := fun x => x.toFun
  coe_injective' := by apply GMetric.ext

instance : GMetricClass (GMetric α β) α β where
  gdist_self := fun x => x.gdist_self
  comm' := fun x => x.comm'
  triangle' := fun x => x.triangle'
  eq_of_dist_eq_zero := GMetric.eq_of_dist_eq_zero

variable {T:Type*} [FunLike T α (α → β)] [GMetricClass T α β] (gdist : T)

#lint
