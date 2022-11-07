/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import Mathlib.Algebra.Group.Basic

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `units M`: the group of units (i.e., invertible elements) of a monoid.
* `is_unit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `add_units` and `is_add_unit`.

## Notation

We provide `Mˣ` as notation for `units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

-/


open Function

universe u

variable {α : Type u}

/-- Units of a `monoid`, bundled version. Notation: `αˣ`.

An element of a `monoid` is a unit if it has a two-sided inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `is_unit`. -/
structure Units (α : Type u) [Monoid α] where
  val : α
  inv : α
  val_inv : val * inv = 1
  inv_val : inv * val = 1

postfix:1024 "ˣ" => Units

-- We don't provide notation for the additive version, because its use is somewhat rare.
/-- Units of an `add_monoid`, bundled version.

An element of an `add_monoid` is a unit if it has a two-sided additive inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `is_add_unit`. -/
structure AddUnits (α : Type u) [AddMonoid α] where
  val : α
  neg : α
  val_neg : val + neg = 0
  neg_val : neg + val = 0

attribute [to_additive] Units
