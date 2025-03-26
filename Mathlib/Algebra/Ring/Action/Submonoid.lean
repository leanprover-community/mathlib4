/-
Copyright (c) 2024 David Ang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ang
-/
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# The subgroup of fixed points of an action
-/

variable (M α : Type*)
instance [Zero α] [SMulZeroClass M α] : ZeroMemClass (FixedPointsType M α) α where
  zero_mem _ := smul_zero

instance [AddMonoid α] [DistribSMul M α] : AddSubmonoidClass (FixedPointsType M α) α where
  add_mem _ {a b} ha hb := fun m => (smul_add m a b).trans congr($(ha m) + $(hb m))

instance [Monoid M] [AddMonoid α] [DistribMulAction M α] :
    AddSubmonoidClass (FixedPointsType M α) α where

instance [Monoid M] [AddGroup α] [DistribMulAction M α] :
    AddSubgroupClass (FixedPointsType M α) α where
  neg_mem _ {_} hx := fun m => smul_neg m _ |>.trans congr(-$(hx m))

variable [Monoid M]

section AddMonoid
variable [AddMonoid α] [DistribMulAction M α]

/-- The additive submonoid of elements fixed under the whole action. -/
abbrev FixedPoints.addSubmonoid : AddSubmonoid α := AddSubmonoid.ofClass <| fixedPointsBundled M α

end AddMonoid

section AddGroup
variable [AddGroup α] [DistribMulAction M α]

/-- The additive subgroup of elements fixed under the whole action. -/
abbrev FixedPoints.addSubgroup : AddSubgroup α := AddSubgroup.ofClass <| fixedPointsBundled M α

end AddGroup
