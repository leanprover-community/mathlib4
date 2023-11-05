/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.OrderSynonym
import Mathlib.Algebra.Order.Monoid.Cancel.Defs

#align_import algebra.order.monoid.order_dual from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-! # Ordered monoid structures on the order dual. -/


universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
instance contravariantClass_mul_le [LE α] [Mul α] [c : ContravariantClass α α (· * ·) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariantClass_mul_le [LE α] [Mul α] [c : CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariantClass_swap_mul_le [LE α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariantClass_swap_mul_le [LE α] [Mul α]
    [c : CovariantClass α α (swap (· * ·)) (· ≤ ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariantClass_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariantClass_mul_lt [LT α] [Mul α] [c : CovariantClass α α (· * ·) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (· * ·) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariantClass_swap_mul_lt [LT α] [Mul α]
    [c : ContravariantClass α α (swap (· * ·)) (· < ·)] :
    ContravariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariantClass_swap_mul_lt [LT α] [Mul α]
    [c : CovariantClass α α (swap (· * ·)) (· < ·)] :
    CovariantClass αᵒᵈ αᵒᵈ (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance orderedCommMonoid [OrderedCommMonoid α] : OrderedCommMonoid αᵒᵈ :=
  { OrderDual.instPartialOrder α, OrderDual.instCommMonoid with
    mul_le_mul_left := fun _ _ h c => mul_le_mul_left' h c }

@[to_additive OrderDual.OrderedCancelAddCommMonoid.to_contravariantClass]
instance OrderedCancelCommMonoid.to_contravariantClass [OrderedCancelCommMonoid α] :
    ContravariantClass αᵒᵈ αᵒᵈ Mul.mul LE.le where
    -- Porting note: We need to specify the implicit arguments here because of
    -- https://github.com/leanprover/lean4/issues/1892
    -- We should be able to remove this after nightly-2022-11-30 arrives.
    elim a b c := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ a c b
-- Porting note: Lean 3 to_additive name omits first namespace part

@[to_additive]
instance orderedCancelCommMonoid [OrderedCancelCommMonoid α] : OrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.orderedCommMonoid, @OrderDual.instCancelCommMonoid α _ with
    le_of_mul_le_mul_left := fun _ _ _ : α => le_of_mul_le_mul_left' }

@[to_additive]
instance linearOrderedCancelCommMonoid [LinearOrderedCancelCommMonoid α] :
    LinearOrderedCancelCommMonoid αᵒᵈ :=
  { OrderDual.instLinearOrder α, OrderDual.orderedCancelCommMonoid with }

@[to_additive]
instance linearOrderedCommMonoid [LinearOrderedCommMonoid α] : LinearOrderedCommMonoid αᵒᵈ :=
  { OrderDual.instLinearOrder α, OrderDual.orderedCommMonoid with }

end OrderDual
