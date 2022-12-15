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

@[to_additive]
instance [OrderedCommGroup α] : OrderedCommGroup αᵒᵈ :=
  { OrderDual.instOrderedCommMonoidOrderDual, instGroupOrderDual with }
#align order_dual.ordered_comm_group instOrderedCommGroupOrderDual
#align order_dual.ordered_add_comm_group instOrderedAddCommGroupOrderDual

@[to_additive]
instance [LinearOrderedCommGroup α] : LinearOrderedCommGroup αᵒᵈ :=
  { instOrderedCommGroupOrderDual, OrderDual.instLinearOrderOrderDual α with }
