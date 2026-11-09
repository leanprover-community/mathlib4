/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, a one-field structure around `Set α`, which we endow with
`∪` as addition and pointwise `*` as multiplication. If `α` is a (commutative) monoid,
`SetSemiring α` is an idempotent (commutative) semiring.
-/

@[expose] public section

open Set
open scoped Pointwise

variable {α β γ : Type*}

/-- `SetSemiring α` is a one-field structure around `Set α` with a semiring structure given by
`∪` as addition and pointwise multiplication `*` as multiplication. -/
@[ext]
structure SetSemiring (α : Type*) where
  /-- Convert a `Set α` to a `SetSemiring α`. -/
  ofSet ::
  /-- The underlying set -/
  toSet : Set α
deriving Inhabited

namespace SetSemiring

/-- The natural equivalence between `SetSemiring α` and `Set α`. -/
@[simps]
def toSetEquiv : SetSemiring α ≃ Set α where
  toFun := toSet
  invFun := ofSet

instance : CompleteAtomicBooleanAlgebra (SetSemiring α) := fast_instance%
  toSetEquiv.completeAtomicBooleanAlgebra

@[simp] lemma toSet_ofSet (s : Set α) : (ofSet s).toSet = s := rfl
@[simp] lemma ofSet_toSet (s : SetSemiring α) : ofSet s.toSet = s := rfl
@[simp] lemma ofSet_le_ofSet {s t : Set α} : ofSet s ≤ ofSet t ↔ s ⊆ t := Iff.rfl
@[simp] lemma ofSet_lt_ofSet {s t : Set α} : ofSet s < ofSet t ↔ s ⊂ t := Iff.rfl
@[simp] lemma toSet_subset_toSet {s t : SetSemiring α} : s.toSet ⊆ t.toSet ↔ s ≤ t := Iff.rfl
@[simp] lemma toSet_ssubset_toSet {s t : SetSemiring α} : s.toSet ⊂ t.toSet ↔ s < t := Iff.rfl

instance : Membership α (SetSemiring α) where mem s a := a ∈ s.toSet
instance : Singleton α (SetSemiring α) where singleton a := ofSet {a}
instance : Insert α (SetSemiring α) where insert a s := ofSet (insert a s.toSet)

@[simp] lemma mem_toSet {s : SetSemiring α} {a : α} : a ∈ s.toSet ↔ a ∈ s := Iff.rfl
@[simp] lemma mem_ofSet {s : Set α} {a : α} : a ∈ ofSet s ↔ a ∈ s := Iff.rfl
@[simp] lemma mem_singleton_iff {a b : α} : a ∈ ({b} : SetSemiring α) ↔ a = b := Iff.rfl
@[simp] lemma toSet_singleton {a : α} : toSet {a} = {a} := rfl
@[simp] lemma ofSet_singleton {a : α} : ofSet {a} = {a} := rfl
@[simp] lemma toSet_insert {s : SetSemiring α} {a : α} : (insert a s).toSet = insert a s.toSet :=
  rfl
@[simp] lemma ofSet_insert {s : Set α} {a : α} : ofSet (insert a s) = insert a (ofSet s) := rfl

instance : Zero (SetSemiring α) where zero := ofSet ∅
instance : Add (SetSemiring α) where add s t := ofSet (s.toSet ∪ t.toSet)

lemma zero_def : (0 : SetSemiring α) = ofSet ∅ := rfl
@[simp] lemma toSet_zero : (0 : SetSemiring α).toSet = ∅ := rfl
@[simp] lemma ofSet_empty : ofSet (∅ : Set α) = 0 := rfl
lemma add_def (s t : SetSemiring α) : s + t = ofSet (s.toSet ∪ t.toSet) := rfl
@[simp] lemma toSet_add (s t : SetSemiring α) : (s + t).toSet = s.toSet ∪ t.toSet := rfl
@[simp] lemma ofSet_union (s t : Set α) : ofSet (s ∪ t) = ofSet s + ofSet t := rfl

instance : AddCommMonoid (SetSemiring α) where
  add_assoc _ _ _ := SetSemiring.ext (union_assoc ..)
  zero_add _ := SetSemiring.ext (empty_union _)
  add_zero _ := SetSemiring.ext (union_empty _)
  add_comm _ _ := SetSemiring.ext (union_comm ..)
  nsmul := nsmulRec

instance : AddLeftMono (SetSemiring α) where
  elim _ _ _ := union_subset_union_right _

section Mul

variable [Mul α]

instance : NonUnitalNonAssocSemiring (SetSemiring α) where
  mul s t := ofSet (s.toSet * t.toSet)
  zero_mul _ := SetSemiring.ext empty_mul
  mul_zero _ := SetSemiring.ext mul_empty
  left_distrib _ _ _ := SetSemiring.ext mul_union
  right_distrib _ _ _ := SetSemiring.ext union_mul

lemma mul_def (s t : SetSemiring α) : s * t = ofSet (s.toSet * t.toSet) := rfl
@[simp] lemma toSet_mul (s t : SetSemiring α) : (s * t).toSet = s.toSet * t.toSet := rfl
@[simp] lemma ofSet_mul (s t : Set α) : ofSet (s * t) = ofSet s * ofSet t := rfl

instance : NoZeroDivisors (SetSemiring α) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by simp [SetSemiring.ext_iff]

instance : MulLeftMono (SetSemiring α) where
  elim _ _ _ := mul_subset_mul_left

instance : MulRightMono (SetSemiring α) where
  elim _ _ _ := mul_subset_mul_right

end Mul

section One

variable [One α]

instance : One (SetSemiring α) where one := ofSet 1

lemma one_def : (1 : SetSemiring α) = ofSet 1 := rfl
@[simp] lemma toSet_one : (1 : SetSemiring α).toSet = 1 := rfl
@[simp] lemma ofSet_one : ofSet (1 : Set α) = 1 := rfl

end One

instance [MulOneClass α] : MulOneClass (SetSemiring α) := fast_instance%
  toSetEquiv.injective.mulOneClass toSet rfl fun _ _ ↦ rfl

instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) where

instance [Semigroup α] : Semigroup (SetSemiring α) := fast_instance%
  toSetEquiv.injective.semigroup toSet fun _ _ ↦ rfl

instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) where

instance [Monoid α] : IdemSemiring (SetSemiring α) where

instance [CommSemigroup α] : CommSemigroup (SetSemiring α) := fast_instance%
  toSetEquiv.injective.commSemigroup toSet fun _ _ ↦ rfl

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) where

instance [CommMonoid α] : CommMonoid (SetSemiring α) := fast_instance%
  toSetEquiv.injective.commMonoid toSet rfl (fun _ _ ↦ rfl)
    fun _ n ↦ by induction n <;> simp [*, pow_succ]

instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) where

instance : CanonicallyOrderedAdd (SetSemiring α) where
  exists_add_of_le {_ b} ab := ⟨b, SetSemiring.ext (union_eq_right.2 ab).symm⟩
  le_add_self _ _ := subset_union_right
  le_self_add _ _ := subset_union_left

instance [CommMonoid α] : IsOrderedRing (SetSemiring α) where

/-- If `α` is a monoid, the map that sends `a : α` to `{a}` is a monoid homomorphism. -/
def singletonMonoidHom [Monoid α] : α →* SetSemiring α where
  toFun a := {a}
  map_one' := rfl
  map_mul' _ _ := SetSemiring.ext image2_singleton.symm

section ImageHom

variable [MulOneClass α] [MulOneClass β] [MulOneClass γ] (f : α →* β)

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def imageHom : SetSemiring α →+* SetSemiring β where
  toFun s := ofSet (f '' s.toSet)
  map_zero' := SetSemiring.ext (image_empty _)
  map_one' := by rw [toSet_one, image_one, map_one, singleton_one, ofSet_one]
  map_add' _ _ := SetSemiring.ext (image_union ..)
  map_mul' _ _ := SetSemiring.ext (image_mul f)

@[simp] lemma imageHom_apply (s : SetSemiring α) : imageHom f s = ofSet (f '' s.toSet) := rfl

@[simp] lemma imageHom_id : imageHom (MonoidHom.id α) = RingHom.id (SetSemiring α) := by
  simp [imageHom, RingHom.id]

lemma imageHom_comp (g : β →* γ) : imageHom (g.comp f) = (imageHom g).comp (imageHom f) := by
  ext; simp

end ImageHom

@[deprecated (since := "2026-10-13")] alias _root_.Set.up := ofSet
@[deprecated (since := "2026-10-13")] alias down := toSet
@[deprecated (since := "2026-10-13")] alias down_up := toSet_ofSet
@[deprecated (since := "2026-10-13")] alias up_down := ofSet_toSet
@[deprecated (since := "2026-10-13")] alias up_le_up := ofSet_le_ofSet
@[deprecated (since := "2026-10-13")] alias up_lt_up := ofSet_lt_ofSet
@[deprecated (since := "2026-10-13")] alias down_subset_down := toSet_subset_toSet
@[deprecated (since := "2026-10-13")] alias down_ssubset_down := toSet_ssubset_toSet
@[deprecated (since := "2026-10-13")] alias down_zero := toSet_zero
@[deprecated (since := "2026-10-13")] alias _root_.Set.up_empty := ofSet_empty
@[deprecated (since := "2026-10-13")] alias down_add := toSet_add
@[deprecated (since := "2026-10-13")] alias _root_.Set.up_union := ofSet_union
@[deprecated (since := "2026-10-13")] alias down_mul := toSet_mul
@[deprecated (since := "2026-10-13")] alias _root_.Set.up_mul := ofSet_mul
@[deprecated (since := "2026-10-13")] alias down_one := toSet_one
@[deprecated (since := "2026-10-13")] alias _root_.Set.up_one := ofSet_one
@[deprecated (since := "2026-10-13")] alias imageHom_def := imageHom_apply
@[deprecated (since := "2026-10-13")] alias down_imageHom := imageHom_apply
@[deprecated (since := "2026-10-13")] alias _root_.Set.up_image := imageHom_apply
@[deprecated "type changed" (since := "2026-11-09")] alias symm_toSet := ofSet_toSet
@[deprecated "type changed" (since := "2026-11-09")] alias symm_ofSet := toSet_ofSet

end SetSemiring
