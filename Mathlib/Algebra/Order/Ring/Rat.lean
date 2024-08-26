/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# The rational numbers form a linear ordered field

This file constructs the order on `ℚ` and proves that `ℚ` is a discrete, linearly ordered
commutative ring.

`ℚ` is in fact a linearly ordered field, but this fact is located in `Data.Rat.Field` instead of
here because we need the order on `ℚ` to define `ℚ≥0`, which we itself need to define `Field`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

assert_not_exists Field
assert_not_exists Finset
assert_not_exists Set.Icc
assert_not_exists GaloisConnection

namespace Rat

instance instLinearOrderedCommRing : LinearOrderedCommRing ℚ where
  __ := Rat.linearOrder
  __ := Rat.commRing
  zero_le_one := by decide
  add_le_add_left := fun a b ab c => Rat.add_le_add_left.2 ab
  mul_pos a b ha hb := (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')

-- Extra instances to short-circuit type class resolution
instance : LinearOrderedRing ℚ := by infer_instance

instance : OrderedRing ℚ := by infer_instance

instance : LinearOrderedSemiring ℚ := by infer_instance

instance : OrderedSemiring ℚ := by infer_instance

instance : LinearOrderedAddCommGroup ℚ := by infer_instance

instance : OrderedAddCommGroup ℚ := by infer_instance

instance : OrderedCancelAddCommMonoid ℚ := by infer_instance

instance : OrderedAddCommMonoid ℚ := by infer_instance

end Rat
