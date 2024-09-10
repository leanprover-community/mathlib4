/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Order.Group.Defs

/-!
# The integers form a linear ordered group

This file contains the linear ordered group instance on the integers.

See note [foundational algebra order theory].

-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

assert_not_exists Ring

open Function Nat

namespace Int

instance linearOrderedAddCommGroup : LinearOrderedAddCommGroup ℤ where
  __ := instLinearOrder
  __ := instAddCommGroup
  add_le_add_left _ _ := Int.add_le_add_left

end Int
