/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Synonym

/-!
# Group with zero structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `Lex α`.
-/

public section


open Function

variable {α : Type*}


/-! ### Order dual -/


namespace OrderDual

instance [h : MulZeroClass α] : MulZeroClass αᵒᵈ where
  zero_mul := h.zero_mul
  mul_zero := h.mul_zero

instance [h : MulZeroOneClass α] : MulZeroOneClass αᵒᵈ where

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors αᵒᵈ where
  eq_zero_or_eq_zero_of_mul_eq_zero := h.eq_zero_or_eq_zero_of_mul_eq_zero

instance [h : SemigroupWithZero α] : SemigroupWithZero αᵒᵈ where

instance [h : MonoidWithZero α] : MonoidWithZero αᵒᵈ where

instance [Mul α] [Zero α] [h : IsLeftCancelMulZero α] : IsLeftCancelMulZero αᵒᵈ where
  mul_left_cancel_of_ne_zero := h.mul_left_cancel_of_ne_zero

instance [Mul α] [Zero α] [h : IsRightCancelMulZero α] : IsRightCancelMulZero αᵒᵈ where
  mul_right_cancel_of_ne_zero := h.mul_right_cancel_of_ne_zero

instance [Mul α] [Zero α] [h : IsCancelMulZero α] : IsCancelMulZero αᵒᵈ where

instance [h : CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ where

instance [h : GroupWithZero α] : GroupWithZero αᵒᵈ where
  inv_zero := h.inv_zero
  mul_inv_cancel := h.mul_inv_cancel

instance [h : CommGroupWithZero α] : CommGroupWithZero αᵒᵈ where

end OrderDual

/-! ### Lexicographic order -/


namespace Lex

instance [MulZeroClass α] : MulZeroClass (Lex α) := inferInstanceAs <| MulZeroClass α

instance [MulZeroOneClass α] : MulZeroOneClass (Lex α) := inferInstanceAs <| MulZeroOneClass α

instance [Mul α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors (Lex α) :=
  inferInstanceAs <| NoZeroDivisors α

instance [SemigroupWithZero α] : SemigroupWithZero (Lex α) := inferInstanceAs <| SemigroupWithZero α

instance [MonoidWithZero α] : MonoidWithZero (Lex α) := inferInstanceAs <| MonoidWithZero α

instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero (Lex α) :=
  inferInstanceAs <| IsLeftCancelMulZero α

instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero (Lex α) :=
  inferInstanceAs <| IsRightCancelMulZero α

instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero (Lex α) :=
  inferInstanceAs <| IsCancelMulZero α

instance [CommMonoidWithZero α] : CommMonoidWithZero (Lex α) :=
  inferInstanceAs <| CommMonoidWithZero α

instance [GroupWithZero α] : GroupWithZero (Lex α) := inferInstanceAs <| GroupWithZero α

instance [CommGroupWithZero α] : CommGroupWithZero (Lex α) := inferInstanceAs <| CommGroupWithZero α

end Lex
