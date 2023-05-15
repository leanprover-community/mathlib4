/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.instances
! leanprover-community/mathlib commit 55bbb8076236154a4f53939a62ad1e4fddbc14c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.OrderDual

/-!
# Additional instances for ordered commutative groups.

-/


variable {α : Type _}

@[to_additive]
instance OrderDual.orderedCommGroup [OrderedCommGroup α] : OrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommMonoid, instGroupOrderDual with }
#align order_dual.ordered_comm_group OrderDual.orderedCommGroup
#align order_dual.ordered_add_comm_group OrderDual.orderedAddCommGroup

@[to_additive]
instance OrderDual.linearOrderedCommGroup [LinearOrderedCommGroup α] : LinearOrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommGroup, OrderDual.linearOrder α with }
