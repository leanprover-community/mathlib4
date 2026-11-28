/-
Copyright (c) 2026 Pavel Zorin-Kranich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Zorin-Kranich
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.OrderOnOrders

/-!
# Discrete order on monoids
-/

public section

namespace PartialOrder.DiscreteOrder

variable {α : Type*} [PartialOrder α] [hd : PartialOrder.DiscreteOrder α]

/-- Addition preserves the discrete order. -/
instance isOrderedAddMonoid [AddCommMonoid α] : IsOrderedAddMonoid α where
  add_le_add_left _ _ h _ := by
    rw [hd.eq_bot] at h ⊢
    congr

end PartialOrder.DiscreteOrder
