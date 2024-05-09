/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Units

#align_import algebra.order.group.units from "leanprover-community/mathlib"@"a95b16cbade0f938fc24abd05412bde1e84bab9b"

/-!
# The units of an ordered commutative monoid form an ordered commutative group
-/


variable {α : Type*}

/-- The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive
      "The units of an ordered commutative additive monoid form an ordered commutative
      additive group."]
instance Units.orderedCommGroup [OrderedCommMonoid α] : OrderedCommGroup αˣ :=
  { Units.instPartialOrderUnits, Units.instCommGroupUnits with
    mul_le_mul_left := fun _ _ h _ => (@mul_le_mul_left' α _ _ _ _ _ h _) }
#align units.ordered_comm_group Units.orderedCommGroup
#align add_units.ordered_add_comm_group AddUnits.orderedAddCommGroup

-- Porting note: the mathlib3 proof was
-- mul_le_mul_left := fun a b h c => (mul_le_mul_left' (h : (a : α) ≤ b) _ : (c : α) * a ≤ c * b) }
-- see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/elaboration.20failure.20in.20algebra.2Eorder.2Egroup.2Eunits
