/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

#align_import algebra.order.monoid.order_dual from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-! # Unbundled ordered monoid structures on the order dual. -/


universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
instance contravariantClass_mul_le [LE α] [Mul α] [c : ContravariantClass α α (· * ·) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_add_le OrderDual.contravariantClass_add_le
#align order_dual.contravariant_class_mul_le OrderDual.contravariantClass_mul_le

@[to_additive]
instance covariantClass_mul_le [LE α] [Mul α] [c : CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_add_le OrderDual.covariantClass_add_le
#align order_dual.covariant_class_mul_le OrderDual.covariantClass_mul_le

@[to_additive]
instance contravariantClass_swap_mul_le [LE α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_swap_add_le OrderDual.contravariantClass_swap_add_le
#align order_dual.contravariant_class_swap_mul_le OrderDual.contravariantClass_swap_mul_le

@[to_additive]
instance covariantClass_swap_mul_le [LE α] [Mul α]
    [c : CovariantClass α α (swap (· * ·)) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_swap_add_le OrderDual.covariantClass_swap_add_le
#align order_dual.covariant_class_swap_mul_le OrderDual.covariantClass_swap_mul_le

@[to_additive]
instance contravariantClass_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_add_lt OrderDual.contravariantClass_add_lt
#align order_dual.contravariant_class_mul_lt OrderDual.contravariantClass_mul_lt

@[to_additive]
instance covariantClass_mul_lt [LT α] [Mul α] [c : CovariantClass α α (· * ·) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_add_lt OrderDual.covariantClass_add_lt
#align order_dual.covariant_class_mul_lt OrderDual.covariantClass_mul_lt

@[to_additive]
instance contravariantClass_swap_mul_lt [LT α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.contravariant_class_swap_add_lt OrderDual.contravariantClass_swap_add_lt
#align order_dual.contravariant_class_swap_mul_lt OrderDual.contravariantClass_swap_mul_lt

@[to_additive]
instance covariantClass_swap_mul_lt [LT α] [Mul α]
    [c : CovariantClass α α (swap (· * ·)) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩
#align order_dual.covariant_class_swap_add_lt OrderDual.covariantClass_swap_add_lt
#align order_dual.covariant_class_swap_mul_lt OrderDual.covariantClass_swap_mul_lt


