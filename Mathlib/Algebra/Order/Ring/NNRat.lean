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
# The nonnegative rational numbers form a linear ordered semiring

This file constructs the order on `ℚ≥0` and proves that `ℚ` is a linearly ordered commutative
semiring.

`ℚ≥0` is in fact a linearly ordered field, but this fact is located in `Data.Rat.Field` instead of
here because we need the order on `ℚ` to define `ℚ≥0`, which we itself need to define `Field`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

assert_not_exists Field Finset

public section

namespace NNRat

instance : IsStrictOrderedRing ℚ≥0 := Nonneg.isStrictOrderedRing

deriving instance OrderedSub, CanonicallyOrderedAdd for NNRat

end NNRat
