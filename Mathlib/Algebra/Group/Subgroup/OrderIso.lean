/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
-/

namespace OrderMonoidIso

@[simps!]
def subgroupCongr {G : Type*} [Group G] [Preorder G] {H K : Subgroup G} (h : H = K) :
    H ≃*o K where
  toMulEquiv := .subgroupCongr h
  map_le_map_iff' := .rfl

@[simps!]
def topSubgroup (G : Type*) [Group G] [Preorder G] : (⊤ : Subgroup G) ≃*o G where
  toMulEquiv := Subgroup.topEquiv
  map_le_map_iff' := .rfl

end OrderMonoidIso
