/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, a one-field structure enclosing `Set α` with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `SetSemiring α` is a
(commutative) semiring.
-/

@[expose] public section

open Set Pointwise

variable {α β : Type*}

/-- A one-field structure enclosing `Set α`, endowed with a semiring structure given by
`∪` as addition and pointwise multiplication `*` as multiplication. -/
@[ext]
structure SetSemiring (α : Type*) where
  /-- Construct a `SetSemiring` from its underlying set. -/
  ofSet ::
  /-- The underlying set -/
  toSet : Set α
deriving Inhabited

namespace SetSemiring

instance : SetLike (SetSemiring α) α where
  coe := toSet
  coe_injective' _ _ _ := by simp [*, SetSemiring.ext_iff]

/-- The natural equivalence between `SetSemiring` and `Set`. -/
def equiv : SetSemiring α ≃ Set α where
  toFun := toSet
  invFun := ofSet

instance : PartialOrder (SetSemiring α) :=
  equiv.partialOrder

lemma le_def {s t : SetSemiring α} : s ≤ t ↔ s.toSet ⊆ t.toSet := Iff.rfl

instance : OrderBot (SetSemiring α) where
  bot := ⟨∅⟩
  bot_le _ := le_def.mpr (by simp)

protected lemma toSet_ofSet (s : Set α) : (ofSet s).toSet = s := rfl
@[simp] protected lemma ofSet_toSet (s : SetSemiring α) : ofSet s.toSet = s := rfl
@[simp] lemma ofSet_le_ofSet {s t : Set α} : ofSet s ≤ ofSet t ↔ s ⊆ t := Iff.rfl
@[simp] lemma ofSet_lt_ofSet {s t : Set α} : ofSet s < ofSet t ↔ s ⊂ t := Iff.rfl
@[simp] lemma toSet_subset_toSet {s t : SetSemiring α} : s.toSet ⊆ t.toSet ↔ s ≤ t := Iff.rfl
@[simp] lemma toSet_ssubset_toSet {s t : SetSemiring α} : s.toSet ⊂ t.toSet ↔ s < t := Iff.rfl

instance : Zero (SetSemiring α) where zero := ⟨∅⟩
instance : Add (SetSemiring α) where add s t := ⟨s.toSet ∪ t.toSet⟩

lemma zero_def : (0 : SetSemiring α) = ⟨∅⟩ := rfl
@[simp] lemma toSet_zero : (0 : SetSemiring α).toSet = ∅ := rfl
@[simp] lemma _root_.Set.ofSet_empty : ofSet (∅ : Set α) = 0 := rfl
lemma add_def (s t : SetSemiring α) : s + t = ⟨s.toSet ∪ t.toSet⟩ := rfl
@[simp] lemma toSet_add (s t : SetSemiring α) : (s + t).toSet = s.toSet ∪ t.toSet := rfl
@[simp] lemma _root_.Set.ofSet_union (s t : Set α) : ⟨s ∪ t⟩ = ofSet s + ofSet t := rfl

instance : AddCommMonoid (SetSemiring α) where
  add_assoc _ _ _ := by simp_rw [add_def, union_assoc]
  zero_add _ := by rw [zero_def, add_def, empty_union]
  add_zero _ := by rw [zero_def, add_def, union_empty]
  add_comm _ _ := by simp_rw [add_def, union_comm]
  nsmul := nsmulRec

/-- Since addition on `SetSemiring` is commutative (it is set union), there is no need
to also have the instance `AddRightMono (SetSemiring α)`. -/
instance addLeftMono : AddLeftMono (SetSemiring α) where
  elim _ _ _ := union_subset_union_right _

section Mul

variable [Mul α]

instance : Mul (SetSemiring α) where mul s t := ⟨image2 (· * ·) s.toSet t.toSet⟩

lemma mul_def (s t : SetSemiring α) : s * t = ⟨s.toSet * t.toSet⟩ := rfl
@[simp] lemma toSet_mul (s t : SetSemiring α) : (s * t).toSet = s.toSet * t.toSet := rfl
@[simp] lemma _root_.Set.ofSet_mul (s t : Set α) : ofSet (s * t) = ⟨s⟩ * ⟨t⟩ := rfl

instance : NonUnitalNonAssocSemiring (SetSemiring α) where
  zero_mul _ := by rw [mul_def, zero_def, empty_mul]
  mul_zero _ := by rw [mul_def, zero_def, mul_empty]
  left_distrib _ _ _ := by simp_rw [mul_def, add_def, mul_union]
  right_distrib _ _ _ := by simp_rw [mul_def, add_def, union_mul]

instance : NoZeroDivisors (SetSemiring α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} ab := by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    simp_rw [zero_def, mul_def, SetSemiring.ext_iff] at *
    exact a.eq_empty_or_nonempty.imp_right fun ha ↦
      b.eq_empty_or_nonempty.resolve_right fun hb ↦
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab

instance mulLeftMono : MulLeftMono (SetSemiring α) where
  elim _ _ _ := mul_subset_mul_left

instance mulRightMono : MulRightMono (SetSemiring α) where
  elim _ _ _ := mul_subset_mul_right

end Mul

section One

variable [One α]

instance : One (SetSemiring α) where one := ⟨1⟩

lemma one_def : (1 : SetSemiring α) = ⟨1⟩ := rfl
@[simp] lemma toSet_one : (1 : SetSemiring α).toSet = 1 := rfl
@[simp] lemma _root_.Set.ofSet_one : ofSet (1 : Set α) = 1 := rfl

end One

instance instNonAssocSemiring [MulOneClass α] : NonAssocSemiring (SetSemiring α) where
  __ := instNonUnitalNonAssocSemiring
  mul_one _ := by rw [one_def, mul_def, mul_one]
  one_mul _ := by rw [one_def, mul_def, one_mul]

instance instNonUnitalSemiring [Semigroup α] : NonUnitalSemiring (SetSemiring α) where
  __ := instNonUnitalNonAssocSemiring
  __ := equiv.semigroup

instance instIdemSemiring [Monoid α] : IdemSemiring (SetSemiring α) where
  __ := instNonAssocSemiring
  __ := instNonUnitalSemiring
  __ := equiv.semilatticeSup
  __ := instOrderBot

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) where
  __ := instNonUnitalSemiring
  __ := equiv.commSemigroup

instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) where
  __ := instIdemSemiring
  __ := equiv.commMonoid

instance [CommMonoid α] : CommMonoid (SetSemiring α) where
  __ := equiv.monoid
  __ := equiv.commSemigroup

instance : CanonicallyOrderedAdd (SetSemiring α) where
  exists_add_of_le {a b} ab := ⟨b, by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    simp only [SetSemiring.ext_iff, le_def, add_def] at ab ⊢
    exact (union_eq_right.2 ab).symm⟩
  le_add_self _ _ := subset_union_right
  le_self_add _ _ := subset_union_left

instance [CommMonoid α] : IsOrderedRing (SetSemiring α) :=
  CanonicallyOrderedAdd.toIsOrderedRing

/-- If `α` is a monoid, the map that sends `a : α` to `{a}` is a monoid homomorphism. -/
def singletonMonoidHom [Monoid α] : α →* SetSemiring α where
  toFun a := ⟨{a}⟩
  map_one' := rfl
  map_mul' _ _ := by simp [mul_def]

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) : SetSemiring α →+* SetSemiring β where
  toFun s := ⟨f '' s.toSet⟩
  map_zero' := by simp
  map_one' := by simp [singleton_one]
  map_add' := by simp [image_union]
  map_mul' _ _ := by simp [image_mul f]

lemma imageHom_def [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    imageHom f s = ⟨f '' s.toSet⟩ :=
  rfl

@[simp]
lemma toSet_imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    (imageHom f s).toSet = f '' s.toSet :=
  rfl

@[simp]
lemma _root_.Set.ofSet_image [MulOneClass α] [MulOneClass β] (f : α →* β) (s : Set α) :
    ⟨f '' s⟩ = imageHom f ⟨s⟩ :=
  rfl

@[deprecated (since := "2026-04-07")] alias Set.up := SetSemiring.ofSet
@[deprecated (since := "2026-04-07")] alias down := SetSemiring.toSet
@[deprecated (since := "2026-04-07")] alias down_up := SetSemiring.toSet_ofSet
@[deprecated (since := "2026-04-07")] alias up_down := SetSemiring.ofSet_toSet
@[deprecated (since := "2026-04-07")] alias up_le_up := ofSet_le_ofSet
@[deprecated (since := "2026-04-07")] alias up_lt_up := ofSet_lt_ofSet
@[deprecated (since := "2026-04-07")] alias down_subset_down := toSet_subset_toSet
@[deprecated (since := "2026-04-07")] alias down_ssubset_down := toSet_ssubset_toSet
@[deprecated (since := "2026-04-07")] alias down_zero := toSet_zero
@[deprecated (since := "2026-04-07")] alias _root_.Set.up_empty := Set.ofSet_empty
@[deprecated (since := "2026-04-07")] alias down_add := toSet_add
@[deprecated (since := "2026-04-07")] alias _root_.Set.up_union := Set.ofSet_union
@[deprecated (since := "2026-04-07")] alias down_mul := toSet_mul
@[deprecated (since := "2026-04-07")] alias _root_.Set.up_mul := Set.ofSet_mul
@[deprecated (since := "2026-04-07")] alias down_one := toSet_one
@[deprecated (since := "2026-04-07")] alias _root_.Set.up_one := Set.ofSet_one
@[deprecated (since := "2026-04-07")] alias down_imageHom := toSet_imageHom
@[deprecated (since := "2026-04-07")] alias _root_.Set.up_image := Set.ofSet_image

end SetSemiring
