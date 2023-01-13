/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.set.semiring
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Smul

/-!
# Sets as a semiring under union

This file defines `set_semiring α`, an alias of `set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `set_semiring α` is a
(commutative) semiring.
-/


open Function Set

open Pointwise

variable {α β : Type _}

/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
def SetSemiring (α : Type _) : Type _ :=
  Set α deriving Inhabited, PartialOrder, OrderBot
#align set_semiring SetSemiring

/-- The identity function `set α → set_semiring α`. -/
protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _
#align set.up Set.up

namespace SetSemiring

/-- The identity function `set_semiring α → set α`. -/
protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _
#align set_semiring.down SetSemiring.down

@[simp]
protected theorem down_up (s : Set α) : s.up.down = s :=
  rfl
#align set_semiring.down_up SetSemiring.down_up

@[simp]
protected theorem up_down (s : SetSemiring α) : s.down.up = s :=
  rfl
#align set_semiring.up_down SetSemiring.up_down

-- TODO: These lemmas are not tagged `simp` because `set.le_eq_subset` simplifies the LHS
theorem up_le_up {s t : Set α} : s.up ≤ t.up ↔ s ⊆ t :=
  Iff.rfl
#align set_semiring.up_le_up SetSemiring.up_le_up

theorem up_lt_up {s t : Set α} : s.up < t.up ↔ s ⊂ t :=
  Iff.rfl
#align set_semiring.up_lt_up SetSemiring.up_lt_up

@[simp]
theorem down_subset_down {s t : SetSemiring α} : s.down ⊆ t.down ↔ s ≤ t :=
  Iff.rfl
#align set_semiring.down_subset_down SetSemiring.down_subset_down

@[simp]
theorem down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t :=
  Iff.rfl
#align set_semiring.down_ssubset_down SetSemiring.down_ssubset_down

instance : AddCommMonoid (SetSemiring α)
    where
  add s t := (s.down ∪ t.down).up
  zero := (∅ : Set α).up
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm

/- Since addition on `set_semiring` is commutative (it is set union), there is no need
to also have the instance `covariant_class (set_semiring α) (set_semiring α) (swap (+)) (≤)`. -/
instance covariant_class_add : CovariantClass (SetSemiring α) (SetSemiring α) (· + ·) (· ≤ ·) :=
  ⟨fun a b c => union_subset_union_right _⟩
#align set_semiring.covariant_class_add SetSemiring.covariant_class_add

section Mul

variable [Mul α]

instance : NonUnitalNonAssocSemiring (SetSemiring α) :=
  {
    SetSemiring.addCommMonoid with
    mul := fun s t => (image2 (· * ·) s.down t.down).up
    zero_mul := fun s => empty_mul
    mul_zero := fun s => mul_empty
    left_distrib := fun _ _ _ => mul_union
    right_distrib := fun _ _ _ => union_mul }

instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun a b ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

instance covariant_class_mul_left :
    CovariantClass (SetSemiring α) (SetSemiring α) (· * ·) (· ≤ ·) :=
  ⟨fun a b c => mul_subset_mul_left⟩
#align set_semiring.covariant_class_mul_left SetSemiring.covariant_class_mul_left

instance covariant_class_mul_right :
    CovariantClass (SetSemiring α) (SetSemiring α) (swap (· * ·)) (· ≤ ·) :=
  ⟨fun a b c => mul_subset_mul_right⟩
#align set_semiring.covariant_class_mul_right SetSemiring.covariant_class_mul_right

end Mul

instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring,
    Set.mulOneClass with
    one := 1
    mul := (· * ·) }

instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring, Set.semigroup with }

instance [Monoid α] : Semiring (SetSemiring α) :=
  { SetSemiring.nonAssocSemiring, SetSemiring.nonUnitalSemiring with }

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalSemiring, Set.commSemigroup with }

instance [CommMonoid α] : CanonicallyOrderedCommSemiring (SetSemiring α) :=
  { SetSemiring.semiring, Set.commMonoid, SetSemiring.partialOrder _, SetSemiring.orderBot _,
    SetSemiring.no_zero_divisors with
    add_le_add_left := fun a b => add_le_add_left
    exists_add_of_le := fun a b ab => ⟨b, (union_eq_right_iff_subset.2 ab).symm⟩
    le_self_add := subset_union_left }

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) : SetSemiring α →+* SetSemiring β
    where
  toFun := image f
  map_zero' := image_empty _
  map_one' := by rw [image_one, map_one, singleton_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f
#align set_semiring.image_hom SetSemiring.imageHom

end SetSemiring

