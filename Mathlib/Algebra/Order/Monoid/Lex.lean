/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Prod.Lex.Hom

/-!
# Order homomorphisms for products of ordered monoids

This file defines order homomorphisms for products of ordered monoids, for both the plain product
and the lexicographic product.

The product of ordered monoids `α × β` is an ordered monoid itself with both natural inclusions
and projections, making it the coproduct as well.

## TODO

Create the "OrdCommMon" category.

-/

namespace MonoidHom

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

@[to_additive]
lemma inl_mono : Monotone (MonoidHom.inl α β) :=
  fun _ _ ↦ by simp

@[to_additive]
lemma inl_strictMono : StrictMono (MonoidHom.inl α β) :=
  fun _ _ ↦ by simp

@[to_additive]
lemma inr_mono : Monotone (MonoidHom.inr α β) :=
  fun _ _ ↦ by simp

@[to_additive]
lemma inr_strictMono : StrictMono (MonoidHom.inr α β) :=
  fun _ _ ↦ by simp

@[to_additive]
lemma fst_mono : Monotone (MonoidHom.fst α β) :=
  fun _ _ ↦ by simp +contextual [Prod.le_def]

@[to_additive]
lemma snd_mono : Monotone (MonoidHom.snd α β) :=
  fun _ _ ↦ by simp +contextual [Prod.le_def]

end MonoidHom

namespace OrderMonoidHom

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from M to M × N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from M to M × N. -/]
def inl : α →*o α × β where
  __ := MonoidHom.inl _ _
  monotone' := MonoidHom.inl_mono

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from N to M × N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from N to M × N. -/]
def inr : β →*o α × β where
  __ := MonoidHom.inr _ _
  monotone' := MonoidHom.inr_mono

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to M. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to M. -/]
def fst : α × β →*o α where
  __ := MonoidHom.fst _ _
  monotone' := MonoidHom.fst_mono

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to N. -/]
def snd : α × β →*o β where
  __ := MonoidHom.snd _ _
  monotone' := MonoidHom.snd_mono

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from M to the
lexicographic M ×ₗ N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from M to the lexicographic M ×ₗ N. -/]
def inlₗ : α →*o α ×ₗ β where
  __ := (Prod.Lex.toLexOrderHom).comp (inl α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from N to the
lexicographic M ×ₗ N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from N to the lexicographic M ×ₗ N. -/]
def inrₗ : β →*o (α ×ₗ β) where
  __ := Prod.Lex.toLexOrderHom.comp (inr α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from the
lexicographic M ×ₗ N to M. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from the lexicographic M ×ₗ N to M. -/]
def fstₗ : (α ×ₗ β) →*o α where
  toFun p := (ofLex p).fst
  map_one' := rfl
  map_mul' := by simp
  monotone' := Prod.Lex.monotone_fst_ofLex

@[to_additive (attr := simp)]
theorem fst_comp_inl : (fst α β).comp (inl α β) = .id α :=
  rfl

@[to_additive (attr := simp)]
theorem fstₗ_comp_inlₗ : (fstₗ α β).comp (inlₗ α β) = .id α :=
  rfl

@[to_additive (attr := simp)]
theorem snd_comp_inl : (snd α β).comp (inl α β) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem fst_comp_inr : (fst α β).comp (inr α β) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem snd_comp_inr : (snd α β).comp (inr α β) = .id β :=
  rfl

@[to_additive]
theorem inl_mul_inr_eq_mk (m : α) (n : β) : inl α β m * inr α β n = (m, n) := by
  simp

@[to_additive]
theorem inlₗ_mul_inrₗ_eq_toLex (m : α) (n : β) : inlₗ α β m * inrₗ α β n = toLex (m, n) := by
  simp [← toLex_mul]

variable {α β}

@[to_additive]
theorem commute_inl_inr (m : α) (n : β) : Commute (inl α β m) (inr α β n) :=
  Commute.prod (.one_right m) (.one_left n)

@[to_additive]
theorem commute_inlₗ_inrₗ (m : α) (n : β) : Commute (inlₗ α β m) (inrₗ α β n) :=
  Commute.prod (.one_right m) (.one_left n)

end OrderMonoidHom
