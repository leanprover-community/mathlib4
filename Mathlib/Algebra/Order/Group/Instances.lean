/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.OrderDual

#align_import algebra.order.group.instances from "leanprover-community/mathlib"@"55bbb8076236154a4f53939a62ad1e4fddbc14c8"

/-!
# Additional instances for ordered commutative groups.

-/


variable {α : Type*}

@[to_additive]
instance OrderDual.orderedCommGroup [OrderedCommGroup α] : OrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommMonoid, OrderDual.instGroup with }
#align order_dual.ordered_comm_group OrderDual.orderedCommGroup
#align order_dual.ordered_add_comm_group OrderDual.orderedAddCommGroup

@[to_additive]
instance OrderDual.linearOrderedCommGroup [LinearOrderedCommGroup α] : LinearOrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommGroup, OrderDual.instLinearOrder α with }
