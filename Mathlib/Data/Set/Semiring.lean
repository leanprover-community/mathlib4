/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Kleene
import Mathlib.Data.Set.Pointwise.SMul

#align_import data.set.semiring from "leanprover-community/mathlib"@"62e8311c791f02c47451bf14aa2501048e7c2f33"

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, an alias of `Set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `SetSemiring α` is a
(commutative) semiring.
-/


open Function Set

open Pointwise

variable {α β : Type*}

-- Porting note: mathlib3 uses `deriving Inhabited, PartialOrder, OrderBot`
/-- An alias for `Set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
def SetSemiring (α : Type*) : Type _ :=
  Set α
#align set_semiring SetSemiring

noncomputable instance (α : Type*) : Inhabited (SetSemiring α) :=
  (inferInstance : Inhabited (Set _))

instance (α : Type*) : PartialOrder (SetSemiring α) :=
  (inferInstance : PartialOrder (Set _))

instance (α : Type*) : OrderBot (SetSemiring α) :=
  (inferInstance : OrderBot (Set _))

/-- The identity function `Set α → SetSemiring α`. -/
protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _
#align set.up Set.up

namespace SetSemiring

/-- The identity function `SetSemiring α → Set α`. -/
protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _
#align set_semiring.down SetSemiring.down

--Porting note: new, since dot notation doesn't work
open SetSemiring (down)
open Set (up)

--Porting note: dot notation no longer works
@[simp]
protected theorem down_up (s : Set α) : SetSemiring.down (Set.up s) = s :=
  rfl
#align set_semiring.down_up SetSemiring.down_up

--Porting note: dot notation no longer works
@[simp]
protected theorem up_down (s : SetSemiring α) : Set.up (SetSemiring.down s) = s :=
  rfl
#align set_semiring.up_down SetSemiring.up_down

-- TODO: These lemmas are not tagged `simp` because `Set.le_eq_subset` simplifies the LHS
--Porting note: dot notation no longer works
theorem up_le_up {s t : Set α} : Set.up s ≤ Set.up t ↔ s ⊆ t :=
  Iff.rfl
#align set_semiring.up_le_up SetSemiring.up_le_up

--Porting note: dot notation no longer works
theorem up_lt_up {s t : Set α} : Set.up s < Set.up t ↔ s ⊂ t :=
  Iff.rfl
#align set_semiring.up_lt_up SetSemiring.up_lt_up

--Porting note: dot notation no longer works
@[simp]
theorem down_subset_down {s t : SetSemiring α} : SetSemiring.down s ⊆ SetSemiring.down t ↔ s ≤ t :=
  Iff.rfl
#align set_semiring.down_subset_down SetSemiring.down_subset_down

--Porting note: dot notation no longer works
@[simp]
theorem down_ssubset_down {s t : SetSemiring α} : SetSemiring.down s ⊂ SetSemiring.down t ↔ s < t :=
  Iff.rfl
#align set_semiring.down_ssubset_down SetSemiring.down_ssubset_down

--Porting note: dot notation no longer works
instance : AddCommMonoid (SetSemiring α) where
  add s t := Set.up (SetSemiring.down s ∪ SetSemiring.down t)
  zero := Set.up (∅ : Set α)
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm

theorem zero_def : (0 : SetSemiring α) = Set.up ∅ :=
  rfl
#align set_semiring.zero_def SetSemiring.zero_def

@[simp]
theorem down_zero : down (0 : SetSemiring α) = ∅ :=
  rfl
#align set_semiring.down_zero SetSemiring.down_zero

@[simp]
theorem _root_.Set.up_empty : Set.up (∅ : Set α) = 0 :=
  rfl
#align set.up_empty Set.up_empty

theorem add_def (s t : SetSemiring α) : s + t = up (down s ∪ down t) :=
  rfl
#align set_semiring.add_def SetSemiring.add_def

@[simp]
theorem down_add (s t : SetSemiring α) : down (s + t) = down s ∪ down t :=
  rfl
#align set_semiring.down_add SetSemiring.down_add

@[simp]
theorem _root_.Set.up_union (s t : Set α) : up (s ∪ t) = up s + up t :=
  rfl
#align set.up_union Set.up_union

/- Since addition on `SetSemiring` is commutative (it is set union), there is no need
to also have the instance `CovariantClass (SetSemiring α) (SetSemiring α) (swap (+)) (≤)`. -/
instance covariantClass_add : CovariantClass (SetSemiring α) (SetSemiring α) (· + ·) (· ≤ ·) :=
  ⟨fun _ _ _ => union_subset_union_right _⟩
#align set_semiring.covariant_class_add SetSemiring.covariantClass_add

section Mul

variable [Mul α]

--Porting note: dot notation no longer works
instance : NonUnitalNonAssocSemiring (SetSemiring α) :=
  { (inferInstance : AddCommMonoid (SetSemiring α)) with
    mul := fun s t => Set.up (image2 (· * ·) (SetSemiring.down s) (SetSemiring.down t))
    zero_mul := fun _ => empty_mul
    mul_zero := fun _ => mul_empty
    left_distrib := fun _ _ _ => mul_union
    right_distrib := fun _ _ _ => union_mul }

-- TODO: port
theorem mul_def (s t : SetSemiring α) : s * t = up (down s * down t) :=
  rfl
#align set_semiring.mul_def SetSemiring.mul_def

@[simp]
theorem down_mul (s t : SetSemiring α) : down (s * t) = down s * down t :=
  rfl
#align set_semiring.down_mul SetSemiring.down_mul

@[simp]
theorem _root_.Set.up_mul (s t : Set α) : up (s * t) = up s * up t :=
  rfl
#align set.up_mul Set.up_mul

instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun {a b} ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

instance covariantClass_mul_left :
    CovariantClass (SetSemiring α) (SetSemiring α) (· * ·) (· ≤ ·) :=
  ⟨fun _ _ _ => mul_subset_mul_left⟩
#align set_semiring.covariant_class_mul_left SetSemiring.covariantClass_mul_left

instance covariantClass_mul_right :
    CovariantClass (SetSemiring α) (SetSemiring α) (swap (· * ·)) (· ≤ ·) :=
  ⟨fun _ _ _ => mul_subset_mul_right⟩
#align set_semiring.covariant_class_mul_right SetSemiring.covariantClass_mul_right

end Mul


section One

variable [One α]

instance : One (SetSemiring α) where one := Set.up (1 : Set α)

theorem one_def : (1 : SetSemiring α) = Set.up 1 :=
  rfl
#align set_semiring.one_def SetSemiring.one_def

@[simp]
theorem down_one : down (1 : SetSemiring α) = 1 :=
  rfl
#align set_semiring.down_one SetSemiring.down_one

@[simp]
theorem _root_.Set.up_one : up (1 : Set α) = 1 :=
  rfl
#align set.up_one Set.up_one

end One

instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalNonAssocSemiring (SetSemiring α)),
    Set.mulOneClass with
    one := 1
    mul := (· * ·) }

instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalNonAssocSemiring (SetSemiring α)), Set.semigroup with }

instance [Monoid α] : IdemSemiring (SetSemiring α) :=
  { (inferInstance : NonAssocSemiring (SetSemiring α)),
    (inferInstance : NonUnitalSemiring (SetSemiring α)),
    (inferInstance : CompleteBooleanAlgebra (Set α)) with }

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalSemiring (SetSemiring α)), Set.commSemigroup with }

instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) :=
  { (inferInstance : IdemSemiring (SetSemiring α)),
    (inferInstance : CommMonoid (Set α)) with }

instance [CommMonoid α] : CommMonoid (SetSemiring α) :=
  { (inferInstance : Monoid (SetSemiring α)), Set.commSemigroup with }

instance [CommMonoid α] : CanonicallyOrderedCommSemiring (SetSemiring α) :=
  { (inferInstance : Semiring (SetSemiring α)), (inferInstance : CommMonoid (SetSemiring α)),
    (inferInstance : PartialOrder (SetSemiring α)), (inferInstance : OrderBot (SetSemiring α)),
    (inferInstance : NoZeroDivisors (SetSemiring α)) with
    add_le_add_left := fun _ _ => add_le_add_left
    exists_add_of_le := fun {_ b} ab => ⟨b, (union_eq_right_iff_subset.2 ab).symm⟩
    le_self_add := subset_union_left }

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) : SetSemiring α →+* SetSemiring β
    where
  toFun s := up (image f (down s))
  map_zero' := image_empty _
  map_one' := by
    dsimp only  -- porting note: structures do not do this automatically any more
    -- ⊢ ↑up (↑f '' ↑down 1) = 1
    rw [down_one, image_one, map_one, singleton_one, up_one]
    -- 🎉 no goals
  map_add' := image_union _
  map_mul' _ _ := image_mul f
#align set_semiring.image_hom SetSemiring.imageHom

lemma imageHom_def [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    imageHom f s = up (image f (down s)) :=
  rfl
#align set_semiring.image_hom_def SetSemiring.imageHom_def

@[simp]
lemma down_imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    down (imageHom f s) = f '' down s :=
  rfl
#align set_semiring.down_image_hom SetSemiring.down_imageHom

@[simp]
lemma _root_.Set.up_image [MulOneClass α] [MulOneClass β] (f : α →* β) (s : Set α) :
    up (f '' s) = imageHom f (up s) :=
  rfl
#align set.up_image Set.up_image

end SetSemiring
