/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Rat

/-!
# The rational numbers form a linear ordered field

This file constructs the order on `ℚ` and proves that `ℚ` is a discrete, linearly ordered
commutative ring.

`ℚ` is in fact a linearly ordered field, but this fact is located in `Data.Rat.Field` instead of
here because we need the order on `ℚ` to define `ℚ≥0`, which we itself need to define `Field`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

assert_not_exists Field Finset Set.Icc GaloisConnection

namespace Rat

instance instIsOrderedAddMonoid : IsOrderedAddMonoid ℚ where
  add_le_add_left := fun _ _ ab _ => Rat.add_le_add_left.2 ab

instance instZeroLEOneClass : ZeroLEOneClass ℚ where
  zero_le_one := by decide

instance instIsStrictOrderedRing : IsStrictOrderedRing ℚ := .of_mul_pos fun _ _ ha hb ↦
  (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')

end Rat
