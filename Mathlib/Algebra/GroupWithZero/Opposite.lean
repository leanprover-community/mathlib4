/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Opposites of groups with zero
-/

public section

assert_not_exists Ring

variable {α : Type*}

namespace MulOpposite

instance instMulZeroClass [MulZeroClass α] : MulZeroClass αᵐᵒᵖ where
  zero_mul _ := by ext; simp
  mul_zero _ := by ext; simp

instance instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵐᵒᵖ where
  __ := instMulOneClass
  __ := instMulZeroClass

instance instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵐᵒᵖ where
  __ := instSemigroup
  __ := instMulZeroClass

instance instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵐᵒᵖ where
  __ := instMonoid
  __ := instMulZeroOneClass

instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵐᵒᵖ where
  __ := instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
  mul_inv_cancel _ hx := by ext; simp [hx]
  inv_zero := unop_injective inv_zero

instance instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵐᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : _ = op (0 : α)) := by
    rw [← unop_inj, unop_mul, unop_op] at H
    obtain (hy | hx) := eq_zero_or_eq_zero_of_mul_eq_zero H
    · right; simpa using hy
    · left; simpa using hx

instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsRightCancelMulZero αᵐᵒᵖ where
  mul_right_cancel_of_ne_zero h _ _ eq := unop_injective <|
    mul_left_cancel₀ (unop_injective.ne_iff.mpr h) (by simp_rw [← unop_inj] at eq; simp_all)

instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsLeftCancelMulZero αᵐᵒᵖ where
  mul_left_cancel_of_ne_zero h _ _ eq := unop_injective <|
    mul_right_cancel₀ (unop_injective.ne_iff.mpr h) (by simp_rw [← unop_inj] at eq; simp_all)

instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵐᵒᵖ where

@[simp] theorem isLeftCancelMulZero_iff [Mul α] [Zero α] :
    IsLeftCancelMulZero αᵐᵒᵖ ↔ IsRightCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isRightCancelMulZero _ rfl (by simp)
  mpr _ := inferInstance

@[simp] theorem isRightCancelMulZero_iff [Mul α] [Zero α] :
    IsRightCancelMulZero αᵐᵒᵖ ↔ IsLeftCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isLeftCancelMulZero _ rfl (by simp)
  mpr _ := inferInstance

@[simp] theorem isCancelMulZero_iff [Mul α] [Zero α] :
    IsCancelMulZero αᵐᵒᵖ ↔ IsCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isCancelMulZero _ rfl (by simp)
  mpr _ := inferInstance

end MulOpposite

namespace AddOpposite

instance instMulZeroClass [MulZeroClass α] : MulZeroClass αᵃᵒᵖ where
  zero_mul _ := unop_injective <| zero_mul _
  mul_zero _ := unop_injective <| mul_zero _

instance instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵃᵒᵖ where
  __ := instMulOneClass
  __ := instMulZeroClass

instance instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵃᵒᵖ where
  __ := instSemigroup
  __ := instMulZeroClass

instance instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵃᵒᵖ where
  __ := instMonoid
  __ := instMulZeroOneClass

instance instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵃᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
    Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
    (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)

instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵃᵒᵖ where
  __ := instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
  mul_inv_cancel _ hx := unop_injective <| mul_inv_cancel₀ <| unop_injective.ne hx
  inv_zero := unop_injective inv_zero

end AddOpposite
