/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Sub.Defs

/-!
# Products of `OrderedSub` types.
-/

assert_not_exists MonoidWithZero

variable {α β : Type*}

instance Prod.orderedSub
    [Preorder α] [Add α] [Sub α] [OrderedSub α] [Sub β] [Preorder β] [Add β] [OrderedSub β] :
    OrderedSub (α × β) where
  tsub_le_iff_right _ _ _ :=
  ⟨fun w ↦ ⟨tsub_le_iff_right.mp w.1, tsub_le_iff_right.mp w.2⟩,
   fun w ↦ ⟨tsub_le_iff_right.mpr w.1, tsub_le_iff_right.mpr w.2⟩⟩

instance Pi.orderedSub {ι : Type*} {α : ι → Type*}
    [∀ i, Preorder (α i)] [∀ i, Add (α i)] [∀ i, Sub (α i)] [∀ i, OrderedSub (α i)] :
    OrderedSub ((i : ι) → α i) where
  tsub_le_iff_right _ _ _ :=
  ⟨fun w i ↦ tsub_le_iff_right.mp (w i), fun w i ↦ tsub_le_iff_right.mpr (w i)⟩
