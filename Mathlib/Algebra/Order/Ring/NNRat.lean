/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Nonneg.Ring
public import Mathlib.Data.NNRat.Defs

/-!
# The nonnegative rational numbers form a linear ordered commutative semiring

This file proves that the linear order on `ℚ≥0` makes it into an ordered semiring.

`ℚ≥0` is in fact a linearly ordered semifield. To access this fact, one must also import
`Mathlib/Algebra/Field/Rat.lean`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

assert_not_exists Field Finset

public section

namespace NNRat

instance : IsStrictOrderedRing ℚ≥0 := Nonneg.isStrictOrderedRing

deriving instance OrderedSub, CanonicallyOrderedAdd for NNRat

end NNRat
