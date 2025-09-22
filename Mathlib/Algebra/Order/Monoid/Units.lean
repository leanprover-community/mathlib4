/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Order.MinMax
import Mathlib.Algebra.Group.Units.Defs

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

@[to_additive (attr := simp, norm_cast)]
theorem val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl

@[to_additive]
instance instPartialOrderUnits [Monoid α] [PartialOrder α] : PartialOrder αˣ :=
  PartialOrder.lift val val_injective

@[to_additive]
instance [Monoid α] [LinearOrder α] : LinearOrder αˣ :=
  LinearOrder.lift' val val_injective

/-- `val : αˣ → α` as an order embedding. -/
@[to_additive (attr := simps -fullyApplied)
  /-- `val : add_units α → α` as an order embedding. -/]
def orderEmbeddingVal [Monoid α] [LinearOrder α] : αˣ ↪o α :=
  ⟨⟨val, val_injective⟩, .rfl⟩

@[to_additive (attr := simp, norm_cast)]
theorem max_val [Monoid α] [LinearOrder α] {a b : αˣ} : (max a b).val = max a.val b.val :=
  Monotone.map_max orderEmbeddingVal.monotone

@[to_additive (attr := simp, norm_cast)]
theorem min_val [Monoid α] [LinearOrder α] {a b : αˣ} : (min a b).val = min a.val b.val :=
  Monotone.map_min orderEmbeddingVal.monotone

end Units
