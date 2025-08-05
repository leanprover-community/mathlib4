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

variable (M α : Type*) [Monoid M]

section AddMonoid
variable [AddMonoid α] [DistribMulAction M α]

/-- The additive submonoid of elements fixed under the whole action. -/
def FixedPoints.addSubmonoid : AddSubmonoid α where
  carrier := MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]

@[simp]
lemma FixedPoints.mem_addSubmonoid (a : α) : a ∈ addSubmonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

end AddMonoid

section AddGroup
variable [AddGroup α] [DistribMulAction M α]

/-- The additive subgroup of elements fixed under the whole action. -/
def FixedPoints.addSubgroup : AddSubgroup α where
  __ := addSubmonoid M α
  neg_mem' ha _ := by rw [smul_neg, ha]

/-- The notation for `FixedPoints.addSubgroup`, chosen to resemble `αᴹ`. -/
notation α "^+" M:51 => FixedPoints.addSubgroup M α

@[simp]
lemma FixedPoints.mem_addSubgroup (a : α) : a ∈ α^+M ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[simp]
lemma FixedPoints.addSubgroup_toAddSubmonoid : (α^+M).toAddSubmonoid = addSubmonoid M α :=
  rfl

end AddGroup
