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
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, an alias of `Set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `SetSemiring α` is a
(commutative) semiring.
-/

@[expose] public section


open Function Set

open Pointwise

variable {α β : Type*}

/-- A one-field structure enclosing `Set α`, endowed with a semiring structure given by
`∪` as "addition" and pointwise multiplication `*` as "multiplication". -/
@[ext]
structure SetSemiring (α : Type*) where
  /-- Construct a `SetSemiring` from its underlying set. -/
  up ::
  /-- The underlying set -/
  down : Set α
deriving Inhabited

@[deprecated (since := "2026-04-03")] alias Set.up := SetSemiring.up

namespace SetSemiring

/-- The natural equivalence between `SetSemiring` and `Set`. -/
def equiv : SetSemiring α ≃ Set α where
  toFun := down
  invFun := up

instance : PartialOrder (SetSemiring α) :=
  equiv.partialOrder

lemma le_def {s t : SetSemiring α} : s ≤ t ↔ s.down ⊆ t.down := Iff.rfl

instance : OrderBot (SetSemiring α) where
  bot := ⟨∅⟩
  bot_le _ := le_def.mpr (by simp)

protected theorem down_up (s : Set α) : (up s).down = s :=
  rfl

@[simp]
protected theorem up_down (s : SetSemiring α) : up s.down = s :=
  rfl

@[simp]
theorem up_le_up {s t : Set α} : up s ≤ up t ↔ s ⊆ t :=
  Iff.rfl

@[simp]
theorem up_lt_up {s t : Set α} : up s < up t ↔ s ⊂ t :=
  Iff.rfl

@[simp]
theorem down_subset_down {s t : SetSemiring α} : s.down ⊆ t.down ↔ s ≤ t :=
  Iff.rfl

@[simp]
theorem down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t :=
  Iff.rfl

instance : Zero (SetSemiring α) where zero := ⟨∅⟩

instance : Add (SetSemiring α) where add s t := ⟨s.down ∪ t.down⟩

theorem zero_def : (0 : SetSemiring α) = ⟨∅⟩ :=
  rfl

@[simp]
theorem down_zero : (0 : SetSemiring α).down = ∅ :=
  rfl

@[simp]
theorem _root_.Set.up_empty : up (∅ : Set α) = 0 :=
  rfl

theorem add_def (s t : SetSemiring α) : s + t = ⟨s.down ∪ t.down⟩ :=
  rfl

@[simp]
theorem down_add (s t : SetSemiring α) : (s + t).down = s.down ∪ t.down :=
  rfl

@[simp]
theorem _root_.Set.up_union (s t : Set α) : ⟨s ∪ t⟩ = up s + up t :=
  rfl

instance : AddCommMonoid (SetSemiring α) where
  add_assoc _ _ _ := by simp_rw [add_def, union_assoc]
  zero_add _ := by simp_rw [zero_def, add_def, empty_union]
  add_zero _ := by simp_rw [zero_def, add_def, union_empty]
  add_comm _ _ := by simp_rw [add_def, union_comm]
  nsmul := nsmulRec

/- Since addition on `SetSemiring` is commutative (it is set union), there is no need
to also have the instance `AddRightMono (SetSemiring α)`. -/
instance addLeftMono : AddLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => union_subset_union_right _⟩

section Mul

variable [Mul α]

instance : Mul (SetSemiring α) where mul s t := ⟨image2 (· * ·) s.down t.down⟩

theorem mul_def (s t : SetSemiring α) : s * t = ⟨s.down * t.down⟩ :=
  rfl

@[simp]
theorem down_mul (s t : SetSemiring α) : (s * t).down = s.down * t.down :=
  rfl

@[simp]
theorem _root_.Set.up_mul (s t : Set α) : up (s * t) = ⟨s⟩ * ⟨t⟩ :=
  rfl

instance : NonUnitalNonAssocSemiring (SetSemiring α) where
  zero_mul _ := by simp_rw [mul_def, zero_def, empty_mul]
  mul_zero _ := by simp_rw [mul_def, zero_def, mul_empty]
  left_distrib _ _ _ := by simp_rw [mul_def, add_def, mul_union]
  right_distrib _ _ _ := by simp_rw [mul_def, add_def, union_mul]

instance : NoZeroDivisors (SetSemiring α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} ab := by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    simp_rw [zero_def, mul_def, SetSemiring.ext_iff] at *
    exact a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab

instance mulLeftMono : MulLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_left⟩

instance mulRightMono : MulRightMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_right⟩

end Mul


section One

variable [One α]

instance : One (SetSemiring α) where one := ⟨1⟩

theorem one_def : (1 : SetSemiring α) = ⟨1⟩ :=
  rfl

@[simp]
theorem down_one : (1 : SetSemiring α).down = 1 :=
  rfl

@[simp]
theorem _root_.Set.up_one : up (1 : Set α) = 1 :=
  rfl

end One

noncomputable instance instNonAssocSemiring [MulOneClass α] : NonAssocSemiring (SetSemiring α) where
  __ := instNonUnitalNonAssocSemiring
  mul_one _ := by simp_rw [one_def, mul_def, mul_one]
  one_mul _ := by simp_rw [one_def, mul_def, one_mul]

instance instNonUnitalSemiring [Semigroup α] : NonUnitalSemiring (SetSemiring α) where
  __ := instNonUnitalNonAssocSemiring
  __ := equiv.semigroup

noncomputable instance instIdemSemiring [Monoid α] : IdemSemiring (SetSemiring α) where
  __ := instNonAssocSemiring
  __ := instNonUnitalSemiring
  __ := equiv.semilatticeSup

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) where
  __ := instNonUnitalSemiring
  __ := equiv.commSemigroup

noncomputable instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) where
  __ := instIdemSemiring
  __ := equiv.commMonoid

noncomputable instance [CommMonoid α] : CommMonoid (SetSemiring α) where
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

noncomputable instance [CommMonoid α] : IsOrderedRing (SetSemiring α) :=
  CanonicallyOrderedAdd.toIsOrderedRing

/-- If `α` is a monoid, the map that sends `a : α` to
the singleton set `{a}` is a monoid homomorphism. -/
noncomputable def singletonMonoidHom [Monoid α] : α →* SetSemiring α where
  toFun a := up {a}
  map_one' := rfl
  map_mul' _ _ := by simp [mul_def]

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
noncomputable def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) :
    SetSemiring α →+* SetSemiring β where
  toFun s := ⟨image f s.down⟩
  map_zero' := by simp [image_empty]
  map_one' := by simp_rw [down_one, image_one, map_one, singleton_one, up_one]
  map_add' := by simp [image_union]
  map_mul' _ _ := by simp [image_mul f]

lemma imageHom_def [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    imageHom f s = ⟨image f s.down⟩ :=
  rfl

@[simp]
lemma down_imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    (imageHom f s).down = f '' s.down :=
  rfl

@[simp]
lemma _root_.Set.up_image [MulOneClass α] [MulOneClass β] (f : α →* β) (s : Set α) :
    ⟨f '' s⟩ = imageHom f ⟨s⟩ :=
  rfl

end SetSemiring
