/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Monoid.Units

/-! # Isomorphism of ordered monoids descends to units
-/

/-- An isomorphism of ordered monoids descends to their units. -/
@[simps!]
def OrderMonoidIso.unitsCongr {α β : Type*} [Preorder α] [Monoid α] [Preorder β] [Monoid β]
    (e : α ≃*o β) : αˣ ≃*o βˣ where
  __ := Units.mapEquiv e.toMulEquiv
  map_le_map_iff' {x y} := by simp [← Units.val_le_val]
