/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.OrderSynonym
import Mathlib.Algebra.Order.Monoid.Cancel.Defs

/-! # Ordered monoid structures on the order dual. -/


universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
instance contravariant_class_mul_le [LE α] [Mul α] [c : ContravariantClass α α (· * ·) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_mul_le OrderDual.contravariant_class_mul_le

@[to_additive]
instance covariant_class_mul_le [LE α] [Mul α] [c : CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_mul_le OrderDual.covariant_class_mul_le

@[to_additive]
instance contravariant_class_swap_mul_le [LE α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_swap_mul_le OrderDual.contravariant_class_swap_mul_le

@[to_additive]
instance covariant_class_swap_mul_le [LE α] [Mul α]
    [c : CovariantClass α α (swap (· * ·)) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_swap_mul_le OrderDual.covariant_class_swap_mul_le

@[to_additive]
instance contravariant_class_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_mul_lt OrderDual.contravariant_class_mul_lt

@[to_additive]
instance covariant_class_mul_lt [LT α] [Mul α] [c : CovariantClass α α (· * ·) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_mul_lt OrderDual.covariant_class_mul_lt

@[to_additive]
instance contravariant_class_swap_mul_lt [LT α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_swap_mul_lt OrderDual.contravariant_class_swap_mul_lt

@[to_additive]
instance covariant_class_swap_mul_lt [LT α] [Mul α]
    [c : CovariantClass α α (swap (· * ·)) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_swap_mul_lt OrderDual.covariant_class_swap_mul_lt

@[to_additive]
instance [OrderedCommMonoid α] : OrderedCommMonoid αᵒᵈ :=
  { OrderDual.instPartialOrderOrderDual α, instCommMonoidOrderDual with
    mul_le_mul_left := fun _ _ h c => mul_le_mul_left' h c }

@[to_additive OrderedCancelAddCommMonoid.to_contravariant_class]
instance OrderedCancelCommMonoid.to_contravariant_class [OrderedCancelCommMonoid α] :
    ContravariantClass αᵒᵈ αᵒᵈ Mul.mul LE.le where
    elim a b c := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ a c b
#align
  order_dual.ordered_cancel_comm_monoid.to_contravariant_class
  OrderDual.OrderedCancelCommMonoid.to_contravariant_class

@[to_additive]
instance [OrderedCancelCommMonoid α] : OrderedCancelCommMonoid αᵒᵈ :=
  { instOrderedCommMonoidOrderDual, @instCancelCommMonoidOrderDual α _ with
    le_of_mul_le_mul_left := fun _ _ _ : α => le_of_mul_le_mul_left' }

@[to_additive]
instance [LinearOrderedCancelCommMonoid α] : LinearOrderedCancelCommMonoid αᵒᵈ :=
  { instLinearOrderOrderDual α, instOrderedCancelCommMonoidOrderDual with }

@[to_additive]
instance [LinearOrderedCommMonoid α] : LinearOrderedCommMonoid αᵒᵈ :=
  { instLinearOrderOrderDual α, instOrderedCommMonoidOrderDual with }

end OrderDual
