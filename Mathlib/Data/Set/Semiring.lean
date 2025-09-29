/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Kleene
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, an alias of `Set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `SetSemiring α` is a
(commutative) semiring.
-/


open Function Set

open Pointwise

variable {α β : Type*}

/-- An alias for `Set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
def SetSemiring (α : Type*) : Type _ :=
  Set α
deriving Inhabited, PartialOrder, OrderBot

/-- The identity function `Set α → SetSemiring α`. -/
protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _

namespace SetSemiring

/-- The identity function `SetSemiring α → Set α`. -/
protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _

open SetSemiring (down)
open Set (up)

@[simp]
protected theorem down_up (s : Set α) : s.up.down = s :=
  rfl

@[simp]
protected theorem up_down (s : SetSemiring α) : s.down.up = s :=
  rfl

-- TODO: These lemmas are not tagged `simp` because `Set.le_eq_subset` simplifies the LHS
theorem up_le_up {s t : Set α} : s.up ≤ t.up ↔ s ⊆ t :=
  Iff.rfl

theorem up_lt_up {s t : Set α} : s.up < t.up ↔ s ⊂ t :=
  Iff.rfl

@[simp]
theorem down_subset_down {s t : SetSemiring α} : s.down ⊆ t.down ↔ s ≤ t :=
  Iff.rfl

@[simp]
theorem down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t :=
  Iff.rfl

instance : Zero (SetSemiring α) where zero := (∅ : Set α).up

instance : Add (SetSemiring α) where add s t := (s.down ∪ t.down).up

instance : AddCommMonoid (SetSemiring α) where
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  nsmul := nsmulRec

theorem zero_def : (0 : SetSemiring α) = Set.up ∅ :=
  rfl

@[simp]
theorem down_zero : (0 : SetSemiring α).down = ∅ :=
  rfl

@[simp]
theorem _root_.Set.up_empty : (∅ : Set α).up = 0 :=
  rfl

theorem add_def (s t : SetSemiring α) : s + t = (s.down ∪ t.down).up :=
  rfl

@[simp]
theorem down_add (s t : SetSemiring α) : (s + t).down = s.down ∪ t.down :=
  rfl

@[simp]
theorem _root_.Set.up_union (s t : Set α) : (s ∪ t).up = s.up + t.up :=
  rfl

/- Since addition on `SetSemiring` is commutative (it is set union), there is no need
to also have the instance `AddRightMono (SetSemiring α)`. -/
instance addLeftMono : AddLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => union_subset_union_right _⟩

section Mul

variable [Mul α]

instance : NonUnitalNonAssocSemiring (SetSemiring α) :=
  { (inferInstance : AddCommMonoid (SetSemiring α)) with
    mul := fun s t => (image2 (· * ·) s.down t.down).up
    zero_mul := fun _ => empty_mul
    mul_zero := fun _ => mul_empty
    left_distrib := fun _ _ _ => mul_union
    right_distrib := fun _ _ _ => union_mul }

theorem mul_def (s t : SetSemiring α) : s * t = (s.down * t.down).up :=
  rfl

@[simp]
theorem down_mul (s t : SetSemiring α) : (s * t).down = s.down * t.down :=
  rfl

@[simp]
theorem _root_.Set.up_mul (s t : Set α) : (s * t).up = s.up * t.up :=
  rfl

instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun {a b} ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

instance mulLeftMono : MulLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_left⟩

instance mulRightMono : MulRightMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_right⟩

end Mul


section One

variable [One α]

instance : One (SetSemiring α) where one := (1 : Set α).up

theorem one_def : (1 : SetSemiring α) = Set.up 1 :=
  rfl

@[simp]
theorem down_one : (1 : SetSemiring α).down = 1 :=
  rfl

@[simp]
theorem _root_.Set.up_one : (1 : Set α).up = 1 :=
  rfl

end One

noncomputable instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalNonAssocSemiring (SetSemiring α)),
    Set.mulOneClass with }

instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalNonAssocSemiring (SetSemiring α)), Set.semigroup with }

noncomputable instance [Monoid α] : IdemSemiring (SetSemiring α) :=
  { (inferInstance : NonAssocSemiring (SetSemiring α)),
    (inferInstance : NonUnitalSemiring (SetSemiring α)),
    (inferInstance : CompleteBooleanAlgebra (Set α)) with }

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalSemiring (SetSemiring α)), Set.commSemigroup with }

noncomputable instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) :=
  { (inferInstance : IdemSemiring (SetSemiring α)),
    (inferInstance : CommMonoid (Set α)) with }

noncomputable instance [CommMonoid α] : CommMonoid (SetSemiring α) :=
  { (inferInstance : Monoid (SetSemiring α)), Set.commSemigroup with }

instance : CanonicallyOrderedAdd (SetSemiring α) where
  exists_add_of_le {_ b} ab := ⟨b, (union_eq_right.2 ab).symm⟩
  le_add_self _ _ := subset_union_right
  le_self_add _ _ := subset_union_left

noncomputable instance [CommMonoid α] : IsOrderedRing (SetSemiring α) :=
  CanonicallyOrderedAdd.toIsOrderedRing

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
noncomputable def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) :
    SetSemiring α →+* SetSemiring β where
  toFun s := (image f s.down).up
  map_zero' := image_empty _
  map_one' := by
    rw [down_one, image_one, map_one, singleton_one, up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f

lemma imageHom_def [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    imageHom f s = (image f s.down).up :=
  rfl

@[simp]
lemma down_imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    (imageHom f s).down = f '' s.down :=
  rfl

@[simp]
lemma _root_.Set.up_image [MulOneClass α] [MulOneClass β] (f : α →* β) (s : Set α) :
    (f '' s).up = imageHom f s.up :=
  rfl

end SetSemiring
