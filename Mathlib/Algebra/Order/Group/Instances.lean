/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.OrderDual

/-!
# Additional instances for ordered commutative groups.

-/


variable {α : Type _}

#print OrderedCommGroup.toOrderedCancelCommMonoid /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCommGroup.toOrderedCancelCommMonoid [s : OrderedCommGroup α] :
    OrderedCancelCommMonoid α :=
  { s with le_of_mul_le_mul_left := fun a b c => (mul_le_mul_iff_left a).mp }
#align ordered_comm_group.to_ordered_cancel_comm_monoid OrderedCommGroup.toOrderedCancelCommMonoid
-/

@[to_additive]
instance [OrderedCommGroup α] : OrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommMonoid, OrderDual.group with }

@[to_additive]
instance [LinearOrderedCommGroup α] : LinearOrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommGroup, OrderDual.linearOrder α with }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid
    [LinearOrderedCommGroup α] : LinearOrderedCancelCommMonoid α :=
  { ‹LinearOrderedCommGroup α› with le_of_mul_le_mul_left := fun x y z => le_of_mul_le_mul_left' }
#align
  linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid
