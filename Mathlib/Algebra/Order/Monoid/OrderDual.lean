/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Algebra.Order.Monoid.Defs

/-! # Ordered monoid structures on the order dual. -/

universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
instance isOrderedMonoid [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] :
    IsOrderedMonoid αᵒᵈ :=
  { mul_le_mul_left := fun _ _ h c => mul_le_mul_left' h c }

@[to_additive]
instance isOrderedCancelMonoid [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] :
    IsOrderedCancelMonoid αᵒᵈ :=
  { le_of_mul_le_mul_left := fun _ _ _ : α => le_of_mul_le_mul_left' }

@[to_additive]
instance orderedCommMonoid [OrderedCommMonoid α] : OrderedCommMonoid αᵒᵈ :=
  { mul_le_mul_left := fun _ _ h c => mul_le_mul_left' h c }

@[to_additive OrderDual.OrderedCancelAddCommMonoid.to_mulLeftReflectLE]
instance OrderedCancelCommMonoid.to_mulLeftReflectLE [OrderedCancelCommMonoid α] :
    MulLeftReflectLE αᵒᵈ where
    elim a b c := OrderedCancelCommMonoid.le_of_mul_le_mul_left (α := α) a c b

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
