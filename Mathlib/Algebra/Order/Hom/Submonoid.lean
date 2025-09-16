/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Isomorphism of submonoids of ordered monoids
-/

/-- The top submonoid is order isomorphic to the whole monoid. -/
@[simps!]
def Submonoid.topOrderMonoidIso {α : Type*} [Preorder α] [Monoid α] : (⊤ : Submonoid α) ≃*o α where
  __ := Submonoid.topEquiv
  map_le_map_iff' := Iff.rfl
