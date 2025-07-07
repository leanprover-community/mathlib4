/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Monoid.Units
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

variable {A B F : Type*} [FunLike F A B]
variable [LinearOrderedCommGroupWithZero A] [LinearOrderedCommGroupWithZero B]
variable [MonoidWithZeroHomClass F A B] {f : F}

open WithZero

section Units

/-- Given any linearly ordered commutative group with zero `A`, this is the order isomorphism
between `WithZero Aˣ` with `A`. -/
@[simps!]
def withZeroUnits_OrderIso : WithZero Aˣ ≃o A where
  __ := withZeroUnitsEquiv
  map_rel_iff' {a b} := by
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, withZeroUnitsEquiv_apply, recZeroCoe]
    split
    · exact ⟨fun _ ↦ WithZero.zero_le b, by simp⟩
    · rcases b
      · simpa using compareOfLessAndEq_eq_lt.mp rfl
      rw [Units.val_le_val, ← WithZero.coe_le_coe]
      rfl

/-- Given any linearly ordered commutative group with zero `A`, this is the inclusion of
`WithZero Aˣ` into `A` as an ordered embedding. -/
def withZeroUnits_OrderEmbedding : WithZero Aˣ ↪o A := withZeroUnits_OrderIso.toOrderEmbedding


end Units

section MonoidWithZeroHom

open MonoidWithZeroHom

/-- The inclusion of `valueGroup₀ f` into `B` a a multiplicative homomorphism. -/
def valueGroup₀_MulWithZeroEmbedding : valueGroup₀ f →*₀ B :=
  (withZeroUnitsHom).comp <| WithZero.map' (valueGroup f).subtype

/-- The inclusion of `valueGroup₀ f` into `WithZero Bˣ` as an order embedding. -/
def valueGroup₀_OrderEmbedding : valueGroup₀ f ↪o WithZero Bˣ where
  toFun := WithZero.map' (valueGroup f).subtype
  inj' := WithZero.map'_injective Subtype.val_injective ..
  map_rel_iff' {a b} := by
    refine ⟨fun h ↦ ?_, fun h ↦ WithZero.map'_mono (fun _ _ x ↦ x) h⟩
    · revert a
      simp only [Function.Embedding.coeFn_mk, «forall», map_zero, WithZero.zero_le, imp_self,
        map'_coe, Subgroup.subtype_apply, Subtype.forall, true_and]
      intro a _ h_le
      have hb : b ≠ 0 := by
        intro H
        apply lt_iff_not_ge.mp <| zero_lt_coe a
        grw [h_le, H, map_zero]
      obtain ⟨_, rfl⟩ := ne_zero_iff_exists.mp hb
      simp [coe_le_coe, ge_iff_le, map'_coe, Subgroup.subtype_apply] at h_le ⊢
      exact h_le

/-- The inclusion of `valueGroup₀ f` into `B` as an order embedding. -/
def valueGroup₀_OrderEmbedding' : valueGroup₀ f ↪o B :=
  valueGroup₀_OrderEmbedding.trans withZeroUnits_OrderEmbedding

end MonoidWithZeroHom
