/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Kleene
import Mathlib.Algebra.Order.Ring.Canonical

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

noncomputable instance (α : Type*) : Inhabited (SetSemiring α) :=
  (inferInstance : Inhabited (Set _))

instance (α : Type*) : PartialOrder (SetSemiring α) :=
  (inferInstance : PartialOrder (Set _))

instance (α : Type*) : OrderBot (SetSemiring α) :=
  (inferInstance : OrderBot (Set _))

/-- The identity function `Set α → SetSemiring α`. -/
protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _

namespace SetSemiring

/-- The identity function `SetSemiring α → Set α`. -/
protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _

-- Porting note: new, since dot notation doesn't work
open SetSemiring (down)
open Set (up)

-- Porting note (#11036): dot notation no longer works
@[simp]
protected theorem down_up (s : Set α) : SetSemiring.down (Set.up s) = s :=
  rfl

-- Porting note (#11036): dot notation no longer works
@[simp]
protected theorem up_down (s : SetSemiring α) : Set.up (SetSemiring.down s) = s :=
  rfl

-- TODO: These lemmas are not tagged `simp` because `Set.le_eq_subset` simplifies the LHS
-- Porting note (#11036): dot notation no longer works
theorem up_le_up {s t : Set α} : Set.up s ≤ Set.up t ↔ s ⊆ t :=
  Iff.rfl

-- Porting note (#11036): dot notation no longer works
theorem up_lt_up {s t : Set α} : Set.up s < Set.up t ↔ s ⊂ t :=
  Iff.rfl

-- Porting note (#11036): dot notation no longer works
@[simp]
theorem down_subset_down {s t : SetSemiring α} : SetSemiring.down s ⊆ SetSemiring.down t ↔ s ≤ t :=
  Iff.rfl

-- Porting note (#11036): dot notation no longer works
@[simp]
theorem down_ssubset_down {s t : SetSemiring α} : SetSemiring.down s ⊂ SetSemiring.down t ↔ s < t :=
  Iff.rfl

instance : Zero (SetSemiring α) where zero := Set.up (∅ : Set α)

instance : Add (SetSemiring α) where add s t := Set.up (SetSemiring.down s ∪ SetSemiring.down t)

-- Porting note (#11036): dot notation no longer works
instance : AddCommMonoid (SetSemiring α) where
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  nsmul := nsmulRec

theorem zero_def : (0 : SetSemiring α) = Set.up ∅ :=
  rfl

@[simp]
theorem down_zero : down (0 : SetSemiring α) = ∅ :=
  rfl

@[simp]
theorem _root_.Set.up_empty : Set.up (∅ : Set α) = 0 :=
  rfl

theorem add_def (s t : SetSemiring α) : s + t = up (down s ∪ down t) :=
  rfl

@[simp]
theorem down_add (s t : SetSemiring α) : down (s + t) = down s ∪ down t :=
  rfl

@[simp]
theorem _root_.Set.up_union (s t : Set α) : up (s ∪ t) = up s + up t :=
  rfl

/- Since addition on `SetSemiring` is commutative (it is set union), there is no need
to also have the instance `AddRightMono (SetSemiring α)`. -/
instance addLeftMono : AddLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => union_subset_union_right _⟩

section Mul

variable [Mul α]

-- Porting note (#11036): dot notation no longer works
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

@[simp]
theorem down_mul (s t : SetSemiring α) : down (s * t) = down s * down t :=
  rfl

@[simp]
theorem _root_.Set.up_mul (s t : Set α) : up (s * t) = up s * up t :=
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

instance : One (SetSemiring α) where one := Set.up (1 : Set α)

theorem one_def : (1 : SetSemiring α) = Set.up 1 :=
  rfl

@[simp]
theorem down_one : down (1 : SetSemiring α) = 1 :=
  rfl

@[simp]
theorem _root_.Set.up_one : up (1 : Set α) = 1 :=
  rfl

end One

instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) :=
  { (inferInstance : NonUnitalNonAssocSemiring (SetSemiring α)),
    Set.mulOneClass with }

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
    exists_add_of_le := fun {_ b} ab => ⟨b, (union_eq_right.2 ab).symm⟩
    le_self_add := fun _ _ => subset_union_left }

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) : SetSemiring α →+* SetSemiring β where
  toFun s := up (image f (down s))
  map_zero' := image_empty _
  map_one' := by
    dsimp only  -- Porting note: structures do not do this automatically any more
    rw [down_one, image_one, map_one, singleton_one, up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f

lemma imageHom_def [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    imageHom f s = up (image f (down s)) :=
  rfl

@[simp]
lemma down_imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    down (imageHom f s) = f '' down s :=
  rfl

@[simp]
lemma _root_.Set.up_image [MulOneClass α] [MulOneClass β] (f : α →* β) (s : Set α) :
    up (f '' s) = imageHom f (up s) :=
  rfl

end SetSemiring
