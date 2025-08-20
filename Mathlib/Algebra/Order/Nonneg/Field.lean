/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Canonical
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Semifield structure on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `CanonicallyLinearOrderedSemifield` if `α` is a `LinearOrderedField`.
-/

assert_not_exists abs_inv

open Set

variable {α : Type*}

section NNRat
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

lemma NNRat.cast_nonneg (q : ℚ≥0) : 0 ≤ (q : α) := by
  rw [cast_def]; exact div_nonneg q.num.cast_nonneg q.den.cast_nonneg

lemma nnqsmul_nonneg (q : ℚ≥0) (ha : 0 ≤ a) : 0 ≤ q • a := by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

end NNRat

namespace Nonneg

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

instance inv : Inv { x : α // 0 ≤ x } :=
  ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩

@[simp, norm_cast]
protected theorem coe_inv (a : { x : α // 0 ≤ x }) : ((a⁻¹ : { x : α // 0 ≤ x }) : α) = (a : α)⁻¹ :=
  rfl

@[simp]
theorem inv_mk (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ :=
  rfl

instance div : Div { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast]
protected theorem coe_div (a b : { x : α // 0 ≤ x }) : ((a / b : { x : α // 0 ≤ x }) : α) = a / b :=
  rfl

@[simp]
theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl

instance zpow : Pow { x : α // 0 ≤ x } ℤ :=
  ⟨fun a n => ⟨(a : α) ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast]
protected theorem coe_zpow (a : { x : α // 0 ≤ x }) (n : ℤ) :
    ((a ^ n : { x : α // 0 ≤ x }) : α) = (a : α) ^ n :=
  rfl

@[simp]
theorem mk_zpow (hx : 0 ≤ x) (n : ℤ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ :=
  rfl

instance instNNRatCast : NNRatCast {x : α // 0 ≤ x} := ⟨fun q ↦ ⟨q, q.cast_nonneg⟩⟩
instance instNNRatSMul : SMul ℚ≥0 {x : α // 0 ≤ x} where
  smul q a := ⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg a.2⟩

@[simp, norm_cast] lemma coe_nnratCast (q : ℚ≥0) : (q : {x : α // 0 ≤ x}) = (q : α) := rfl
@[simp] lemma mk_nnratCast (q : ℚ≥0) : (⟨q, q.cast_nonneg⟩ : {x : α // 0 ≤ x}) = q := rfl

@[simp, norm_cast] lemma coe_nnqsmul (q : ℚ≥0) (a : {x : α // 0 ≤ x}) :
    ↑(q • a) = (q • a : α) := rfl
@[simp] lemma mk_nnqsmul (q : ℚ≥0) (a : α) (ha : 0 ≤ a) :
    (⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha⟩ : {x : α // 0 ≤ x}) =
      q • a := rfl

instance semifield : Semifield { x : α // 0 ≤ x } := fast_instance%
  Subtype.coe_injective.semifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) coe_nnqsmul Nonneg.coe_pow
    Nonneg.coe_zpow Nonneg.coe_natCast coe_nnratCast

end LinearOrderedSemifield

instance linearOrderedCommGroupWithZero [Field α] [LinearOrder α] [IsStrictOrderedRing α] :
    LinearOrderedCommGroupWithZero { x : α // 0 ≤ x } :=
  CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

end Nonneg
