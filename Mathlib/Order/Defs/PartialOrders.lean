/-
Copyright (c) 2026 Pavel Zorin-Kranich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Zorin-Kranich
-/
module

public import Mathlib.Order.BoundedOrder.Basic

/-!
# The order on partial orders

Partial orders on a fixed type are ordered by inclusion of their LE relations.
The bottom partial order `⊥` is the discrete order, which is given by the Eq relation.
-/

@[expose] public section

namespace PartialOrder

variable {α : Type*}

instance : PartialOrder (PartialOrder α) :=
  PartialOrder.lift (fun p : PartialOrder α ↦ p.le) (by intro _ _ h; dsimp at h; ext _ _; rw [h])

theorem le_def {p q : PartialOrder α} : p ≤ q ↔ ∀ x y, p.le x y → q.le x y :=
  Iff.rfl

/-- The bottom partial order is the discrete order. -/
instance : OrderBot (PartialOrder α) where
  bot :=
    { le := Eq
      le_refl := Eq.refl
      le_trans _ _ _ := Eq.trans
      le_antisymm _ _ h _ := h }
  bot_le p := by
    rw [le_def]
    intro x y h
    exact le_of_eq h

@[simp] theorem bot_le_iff_eq {x y : α} : (⊥ : PartialOrder α).le x y ↔ x = y :=
  Iff.rfl

/-- This typeclass allows automatic deduction of order properties
for types equipped with the discrete order. -/
class DiscreteOrder (α : Type*) [p : PartialOrder α] : Prop where
  eq_bot : p = ⊥

instance (α : Type*) : @DiscreteOrder α ⊥ :=
  @DiscreteOrder.mk α ⊥ rfl

namespace DiscreteOrder

variable [PartialOrder α] [d : DiscreteOrder α]

theorem le_iff_eq (a b : α) : a ≤ b ↔ a = b := by
  rw [d.eq_bot]
  exact bot_le_iff_eq

end DiscreteOrder

end PartialOrder
