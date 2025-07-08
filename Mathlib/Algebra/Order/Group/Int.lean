/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Monoid.Defs

/-!
# The integers form a linear ordered group

This file contains the instance necessary to show that the integers are a linear ordered
additive group.

See note [foundational algebra order theory].
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton Ring

instance Int.instIsOrderedAddMonoid : IsOrderedAddMonoid ℤ where
  add_le_add_left _ _ := Int.add_le_add_left
