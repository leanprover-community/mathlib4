/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Order.MinMax
import Mathlib.Algebra.Group.Units

#align_import algebra.order.monoid.units from "leanprover-community/mathlib"@"f1a2caaf51ef593799107fe9a8d5e411599f3996"

/-!
# Units in ordered monoids
-/

namespace Units

variable {α : Type*}

@[to_additive]
instance [Monoid α] [Preorder α] : Preorder αˣ :=
  Preorder.lift val

@[to_additive (attr := simp, norm_cast)]
theorem val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl
#align units.coe_le_coe Units.val_le_val
#align add_units.coe_le_coe AddUnits.val_le_val

@[to_additive (attr := simp, norm_cast)]
theorem val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl
#align units.coe_lt_coe Units.val_lt_val
#align add_units.coe_lt_coe AddUnits.val_lt_val

@[to_additive]
instance instPartialOrderUnits [Monoid α] [PartialOrder α] : PartialOrder αˣ :=
  PartialOrder.lift val Units.ext
#align units.partial_order Units.instPartialOrderUnits
#align add_units.partial_order AddUnits.instPartialOrderAddUnits

@[to_additive]
instance [Monoid α] [LinearOrder α] : LinearOrder αˣ :=
  LinearOrder.lift' val Units.ext

/-- `val : αˣ → α` as an order embedding. -/
@[to_additive (attr := simps (config := .asFn))
  "`val : add_units α → α` as an order embedding."]
def orderEmbeddingVal [Monoid α] [LinearOrder α] : αˣ ↪o α :=
  ⟨⟨val, ext⟩, Iff.rfl⟩
#align units.order_embedding_coe Units.orderEmbeddingVal
#align add_units.order_embedding_coe AddUnits.orderEmbeddingVal

@[to_additive (attr := simp, norm_cast)]
theorem max_val [Monoid α] [LinearOrder α] {a b : αˣ} : (max a b).val = max a.val b.val :=
  Monotone.map_max orderEmbeddingVal.monotone
#align units.max_coe Units.max_val
#align add_units.max_coe AddUnits.max_val

@[to_additive (attr := simp, norm_cast)]
theorem min_val [Monoid α] [LinearOrder α] {a b : αˣ} : (min a b).val = min a.val b.val :=
  Monotone.map_min orderEmbeddingVal.monotone
#align units.min_coe Units.min_val
#align add_units.min_coe AddUnits.min_val

end Units
