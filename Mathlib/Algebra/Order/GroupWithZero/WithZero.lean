/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
/-!

# Covariant instances on `WithZero`

Adding a zero to a type with a preorder and multiplication which satisfies some
axiom, gives us a new type which satisfies some variant of the axiom.

## Example

If `α` satisfies `b₁ < b₂ → a * b₁ < a * b₂` for all `a`,
then `WithZero α` satisfies `b₁ < b₂ → a * b₁ < a * b₂` for all `a > 0`,
which is `PosMulStrictMono (WithZero α)`.

## Application

The type `ℤᵐ⁰ := WithZero (Multiplicative ℤ)` is used a lot in mathlib's valuation
theory. These instances enable lemmas such as `mul_pos` to fire on `ℤᵐ⁰`.

-/

assert_not_exists Ring

-- this makes `mul_lt_mul_left`, `mul_pos` etc work on `ℤᵐ⁰`
instance {α : Type*} [Mul α] [Preorder α] [MulLeftStrictMono α] :
    PosMulStrictMono (WithZero α) where
  elim := @fun
    | ⟨(x : α), hx⟩, 0, (b : α), _ => by
        simpa only [mul_zero] using WithZero.zero_lt_coe _
    | ⟨(x : α), hx⟩, (a : α), (b : α), h => by
        dsimp only at h ⊢
        norm_cast at h ⊢
        exact mul_lt_mul_left' h x

open Function in
instance {α : Type*} [Mul α] [Preorder α] [MulRightStrictMono α] :
    MulPosStrictMono (WithZero α) where
  elim := @fun
    | ⟨(x : α), hx⟩, 0, (b : α), _ => by
        simpa only [mul_zero] using WithZero.zero_lt_coe _
    | ⟨(x : α), hx⟩, (a : α), (b : α), h => by
        dsimp only at h ⊢
        norm_cast at h ⊢
        exact mul_lt_mul_right' h x

instance {α : Type*} [Mul α] [Preorder α] [MulLeftMono α] :
    PosMulMono (WithZero α) where
  elim := @fun
    | ⟨0, _⟩, a, b, _ => by
        simp only [zero_mul, le_refl]
    | ⟨(x : α), _⟩, 0, _, _ => by
        simp only [mul_zero, WithZero.zero_le]
    | ⟨(x : α), _⟩, (a : α), 0, h =>
        (lt_irrefl 0 (lt_of_lt_of_le (WithZero.zero_lt_coe a) h)).elim
    | ⟨(x : α), hx⟩, (a : α), (b : α), h => by
        dsimp only at h ⊢
        norm_cast at h ⊢
        exact mul_le_mul_left' h x

-- This makes `lt_mul_of_le_of_one_lt'` work on `ℤᵐ⁰`
open Function in
instance {α : Type*} [Mul α] [Preorder α] [MulRightMono α] :
    MulPosMono (WithZero α) where
  elim := @fun
    | ⟨0, _⟩, a, b, _ => by
        simp only [mul_zero, le_refl]
    | ⟨(x : α), _⟩, 0, _, _ => by
        simp only [zero_mul, WithZero.zero_le]
    | ⟨(x : α), _⟩, (a : α), 0, h =>
        (lt_irrefl 0 (lt_of_lt_of_le (WithZero.zero_lt_coe a) h)).elim
    | ⟨(x : α), hx⟩, (a : α), (b : α), h => by
        dsimp only at h ⊢
        norm_cast at h ⊢
        exact mul_le_mul_right' h x

section Units

variable {α : Type*} [LinearOrderedCommGroupWithZero α]

open WithZero

lemma WithZero.withZeroUnitsEquiv_strictMono :
    StrictMono (withZeroUnitsEquiv (G := α)) := by
  intro a b
  cases a <;> cases b <;>
  simp

/-- Given any linearly ordered commutative group with zero `α`, this is the order isomorphism
between `WithZero αˣ` with `α`. -/
@[simps!]
def OrderIso.withZeroUnits : WithZero αˣ ≃o α where
  __ := withZeroUnitsEquiv
  map_rel_iff' := WithZero.withZeroUnitsEquiv_strictMono.le_iff_le

lemma WithZero.withZeroUnitsEquiv_symm_strictMono :
    StrictMono (withZeroUnitsEquiv (G := α)).symm :=
  OrderIso.withZeroUnits.symm.strictMono

end Units
