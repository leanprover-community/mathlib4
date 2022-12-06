/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Order.MinMax
import Mathbin.Algebra.Group.Units

/-!
# Units in ordered monoids
-/


variable {α : Type _}

namespace Units

@[to_additive]
instance [Monoid α] [Preorder α] : Preorder αˣ :=
  Preorder.lift (coe : αˣ → α)

@[simp, norm_cast, to_additive]
theorem coe_le_coe [Monoid α] [Preorder α] {a b : αˣ} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl
#align units.coe_le_coe Units.coe_le_coe

@[simp, norm_cast, to_additive]
theorem coe_lt_coe [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl
#align units.coe_lt_coe Units.coe_lt_coe

@[to_additive]
instance [Monoid α] [PartialOrder α] : PartialOrder αˣ :=
  PartialOrder.lift coe Units.ext

@[to_additive]
instance [Monoid α] [LinearOrder α] : LinearOrder αˣ :=
  LinearOrder.lift' coe Units.ext

/-- `coe : αˣ → α` as an order embedding. -/
@[to_additive "`coe : add_units α → α` as an order embedding.",
  simps (config := { fullyApplied := false })]
def orderEmbeddingCoe [Monoid α] [LinearOrder α] : αˣ ↪o α :=
  ⟨⟨coe, ext⟩, fun _ _ => Iff.rfl⟩
#align units.order_embedding_coe Units.orderEmbeddingCoe

@[simp, norm_cast, to_additive]
theorem max_coe [Monoid α] [LinearOrder α] {a b : αˣ} : (↑(max a b) : α) = max a b :=
  Monotone.map_max orderEmbeddingCoe.Monotone
#align units.max_coe Units.max_coe

@[simp, norm_cast, to_additive]
theorem min_coe [Monoid α] [LinearOrder α] {a b : αˣ} : (↑(min a b) : α) = min a b :=
  Monotone.map_min orderEmbeddingCoe.Monotone
#align units.min_coe Units.min_coe

end Units

