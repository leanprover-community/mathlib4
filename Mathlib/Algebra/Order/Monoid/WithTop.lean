/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-! # Adjoining top/bottom elements to ordered monoids.
-/

universe u

variable {α : Type u}

open Function

namespace WithTop

instance isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid (WithTop α) where
  add_le_add_left _ _ := add_le_add_left

instance canonicallyOrderedAdd [Add α] [Preorder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedAdd (WithTop α) where
  le_self_add
  | ⊤, _ => le_rfl
  | (a : α), ⊤ => le_top
  | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
  le_add_self
  | ⊤, ⊤ | ⊤, (b : α) => le_rfl
  | (a : α), ⊤ => le_top
  | (a : α), (b : α) => WithTop.coe_le_coe.2 le_add_self

end WithTop

namespace WithBot

instance isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid (WithBot α) :=
  { add_le_add_left := fun _ _ h c => add_le_add_left h c }

protected theorem le_self_add [Add α] [LE α] [CanonicallyOrderedAdd α]
    {x : WithBot α} (hx : x ≠ ⊥) (y : WithBot α) :
    y ≤ y + x := by
  induction x
  · simp at hx
  induction y
  · simp
  · rw [← WithBot.coe_add, WithBot.coe_le_coe]
    exact le_self_add

protected theorem le_add_self [AddCommMagma α] [LE α] [CanonicallyOrderedAdd α]
    {x : WithBot α} (hx : x ≠ ⊥) (y : WithBot α) :
    y ≤ x + y := by
  induction x
  · simp at hx
  induction y
  · simp
  · rw [← WithBot.coe_add, WithBot.coe_le_coe]
    exact le_add_self

end WithBot
