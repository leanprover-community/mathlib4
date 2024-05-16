/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Field.Canonical.Defs
import Mathlib.Algebra.Order.Field.InjSurj
import Mathlib.Algebra.Order.Nonneg.Ring

#align_import algebra.order.nonneg.field from "leanprover-community/mathlib"@"b3f4f007a962e3787aa0f3b5c7942a1317f7d88e"

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
variable [LinearOrderedSemifield α] {a : α}

lemma NNRat.cast_nonneg (q : ℚ≥0) : 0 ≤ (q : α) := by
  rw [cast_def]; exact div_nonneg q.num.cast_nonneg q.den.cast_nonneg

lemma nnqsmul_nonneg (q : ℚ≥0) (ha : 0 ≤ a) : 0 ≤ q • a := by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

end NNRat

namespace Nonneg

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] {x y : α}

instance inv : Inv { x : α // 0 ≤ x } :=
  ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩
#align nonneg.has_inv Nonneg.inv

@[simp, norm_cast]
protected theorem coe_inv (a : { x : α // 0 ≤ x }) : ((a⁻¹ : { x : α // 0 ≤ x }) : α) = (a : α)⁻¹ :=
  rfl
#align nonneg.coe_inv Nonneg.coe_inv

@[simp]
theorem inv_mk (hx : 0 ≤ x) : (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ :=
  rfl
#align nonneg.inv_mk Nonneg.inv_mk

instance div : Div { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩
#align nonneg.has_div Nonneg.div

@[simp, norm_cast]
protected theorem coe_div (a b : { x : α // 0 ≤ x }) : ((a / b : { x : α // 0 ≤ x }) : α) = a / b :=
  rfl
#align nonneg.coe_div Nonneg.coe_div

@[simp]
theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl
#align nonneg.mk_div_mk Nonneg.mk_div_mk

instance zpow : Pow { x : α // 0 ≤ x } ℤ :=
  ⟨fun a n => ⟨(a : α) ^ n, zpow_nonneg a.2 _⟩⟩
#align nonneg.has_zpow Nonneg.zpow

@[simp, norm_cast]
protected theorem coe_zpow (a : { x : α // 0 ≤ x }) (n : ℤ) :
    ((a ^ n : { x : α // 0 ≤ x }) : α) = (a : α) ^ n :=
  rfl
#align nonneg.coe_zpow Nonneg.coe_zpow

@[simp]
theorem mk_zpow (hx : 0 ≤ x) (n : ℤ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ :=
  rfl
#align nonneg.mk_zpow Nonneg.mk_zpow

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

instance linearOrderedSemifield : LinearOrderedSemifield { x : α // 0 ≤ x } :=
  Subtype.coe_injective.linearOrderedSemifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) coe_nnqsmul Nonneg.coe_pow
    Nonneg.coe_zpow Nonneg.coe_natCast coe_nnratCast (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_semifield Nonneg.linearOrderedSemifield

end LinearOrderedSemifield

instance canonicallyLinearOrderedSemifield [LinearOrderedField α] :
    CanonicallyLinearOrderedSemifield { x : α // 0 ≤ x } :=
  { Nonneg.linearOrderedSemifield, Nonneg.canonicallyOrderedCommSemiring with }
#align nonneg.canonically_linear_ordered_semifield Nonneg.canonicallyLinearOrderedSemifield

instance linearOrderedCommGroupWithZero [LinearOrderedField α] :
    LinearOrderedCommGroupWithZero { x : α // 0 ≤ x } :=
  inferInstance
#align nonneg.linear_ordered_comm_group_with_zero Nonneg.linearOrderedCommGroupWithZero

end Nonneg
