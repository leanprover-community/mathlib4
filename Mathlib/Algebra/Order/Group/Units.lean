/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Units

/-!
# Adjoining a top element to a `linear_ordered_add_comm_group_with_top`.
-/


variable {α : Type _}

/-- The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive
      "The units of an ordered commutative additive monoid form an ordered commutative\nadditive group."]
instance Units.orderedCommGroup [OrderedCommMonoid α] : OrderedCommGroup αˣ :=
  { Units.partialOrder, Units.commGroup with
    mul_le_mul_left := fun a b h c => (mul_le_mul_left' (h : (a : α) ≤ b) _ : (c : α) * a ≤ c * b) }
#align units.ordered_comm_group Units.orderedCommGroup
