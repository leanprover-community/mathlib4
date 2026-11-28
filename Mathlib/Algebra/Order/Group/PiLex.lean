/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.PiLex

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Lexicographic product of algebraic order structures

This file proves that the lexicographic order on pi types is compatible with the pointwise algebraic
operations.
-/

public section

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι]
  [∀ i, CommMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsOrderedCancelMonoid (α i)]

@[to_additive]
instance Pi.Lex.isOrderedCancelMonoid : IsOrderedCancelMonoid (Lex (∀ i, α i)) where
  mul_le_mul_left _ _ hxy z :=
    hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hji => congr($(hi.1 j hji) * z.ofLex j), mul_lt_mul_left hi.2 _⟩
  le_of_mul_le_mul_left _ _ _ hxyz :=
    hxyz.elim (fun h => (mul_left_cancel h).le) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hj => (mul_left_cancel <| hi.1 j hj), lt_of_mul_lt_mul_left' hi.2⟩

@[to_additive]
instance Pi.Colex.isOrderedCancelMonoid : IsOrderedCancelMonoid (Colex (∀ i, α i)) where
  mul_le_mul_left _ _ hxy z :=
    hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hji => congr($(hi.1 j hji) * z.ofColex j), mul_lt_mul_left hi.2 _⟩
  le_of_mul_le_mul_left _ _ _ hxyz :=
    hxyz.elim (fun h => (mul_left_cancel h).le) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hj => (mul_left_cancel <| hi.1 j hj), lt_of_mul_lt_mul_left' hi.2⟩
