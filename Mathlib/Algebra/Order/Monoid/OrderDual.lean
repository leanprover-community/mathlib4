/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Algebra.Order.Monoid.Defs

#align_import algebra.order.monoid.order_dual from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-! # Ordered monoid structures on the order dual. -/


universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
instance orderedCommMonoid [OrderedCommMonoid α] : OrderedCommMonoid αᵒᵈ :=
  { mul_le_mul_left := fun _ _ h c => mul_le_mul_left' h c }
#align order_dual.ordered_comm_monoid OrderDual.orderedCommMonoid
#align order_dual.ordered_add_comm_monoid OrderDual.orderedAddCommMonoid

@[to_additive OrderDual.OrderedCancelAddCommMonoid.to_contravariantClass]
instance OrderedCancelCommMonoid.to_contravariantClass [OrderedCancelCommMonoid α] :
    ContravariantClass αᵒᵈ αᵒᵈ HMul.hMul LE.le where
    elim a b c := OrderedCancelCommMonoid.le_of_mul_le_mul_left (α := α) a c b
-- Porting note: Lean 3 to_additive name omits first namespace part
#align ordered_cancel_add_comm_monoid.to_contravariant_class OrderDual.OrderedCancelAddCommMonoid.to_contravariantClass
#align order_dual.ordered_cancel_comm_monoid.to_contravariant_class OrderDual.OrderedCancelCommMonoid.to_contravariantClass

@[to_additive]
instance orderedCancelCommMonoid [OrderedCancelCommMonoid α] : OrderedCancelCommMonoid αᵒᵈ :=
  { le_of_mul_le_mul_left := fun _ _ _ : α => le_of_mul_le_mul_left' }

@[to_additive]
instance linearOrderedCancelCommMonoid [LinearOrderedCancelCommMonoid α] :
    LinearOrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.instLinearOrder α, OrderDual.orderedCancelCommMonoid with }

@[to_additive]
instance linearOrderedCommMonoid [LinearOrderedCommMonoid α] : LinearOrderedCommMonoid αᵒᵈ :=
  { OrderDual.instLinearOrder α, OrderDual.orderedCommMonoid with }

end OrderDual
