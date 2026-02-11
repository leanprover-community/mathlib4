/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# The subgroup of fixed points of an action
-/

@[expose] public section

variable (M α β : Type*) [Monoid M]

namespace FixedPoints

section AddMonoid

variable [AddMonoid α] [DistribMulAction M α] [AddMonoid β] [DistribMulAction M β] {f : α →+ β}

/-- The additive submonoid of elements fixed under the whole action. -/
def addSubmonoid : AddSubmonoid α where
  carrier := MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]

@[simp]
lemma mem_addSubmonoid (a : α) : a ∈ addSubmonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

variable {M α β}

/-- The restriction of a `AddMonoidHom` to `FixedPoints.addSubmonoid`. -/
def addSubmonoidMap (h : ∀ m : M, ∀ a : α, f (m • a) = m • f a) :
    addSubmonoid M α →+ addSubmonoid M β :=
  f.restrict fun _ h' _ => by rw [← h, h']

lemma addSubmonoidMap_injective (h : ∀ m : M, ∀ a : α, f (m • a) = m • f a)
    (hf : Function.Injective f) : Function.Injective <| addSubmonoidMap h :=
  AddMonoidHom.restrict_injective _ hf

end AddMonoid

section AddGroup

variable [AddGroup α] [DistribMulAction M α] [AddGroup β] [DistribMulAction M β] {f : α →+ β}

/-- The additive subgroup of elements fixed under the whole action. -/
def addSubgroup : AddSubgroup α where
  __ := addSubmonoid M α
  neg_mem' ha _ := by rw [smul_neg, ha]

/-- The notation for `FixedPoints.addSubgroup`, chosen to resemble `αᴹ`. -/
notation α "^+" M:51 => addSubgroup M α

@[simp]
lemma mem_addSubgroup (a : α) : a ∈ α^+M ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[simp]
lemma addSubgroup_toAddSubmonoid : (α^+M).toAddSubmonoid = addSubmonoid M α :=
  rfl

variable {M α β}

/-- The restriction of a `AddMonoidHom` to `FixedPoints.addSubgroup`. -/
def addSubgroupMap (h : ∀ m : M, ∀ a : α, f (m • a) = m • f a) : α^+M →+ β^+M :=
  addSubmonoidMap h

lemma addSubgroupMap_injective (h : ∀ m : M, ∀ a : α, f (m • a) = m • f a)
    (hf : Function.Injective f) : Function.Injective <| addSubgroupMap h :=
  addSubmonoidMap_injective h hf

end AddGroup

end FixedPoints
