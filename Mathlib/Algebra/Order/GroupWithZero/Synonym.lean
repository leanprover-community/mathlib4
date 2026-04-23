/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Init
import Mathlib.Util.CompileInductive

/-!
# Group with zero structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `Lex α`.
-/

@[expose] public section


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


instance [h : MulZeroClass α] : MulZeroClass (Lex α) := h

instance [h : MulZeroOneClass α] : MulZeroOneClass (Lex α) := h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors (Lex α) := h

instance [h : SemigroupWithZero α] : SemigroupWithZero (Lex α) := h

instance [h : MonoidWithZero α] : MonoidWithZero (Lex α) := h

instance [Mul α] [Zero α] [h : IsLeftCancelMulZero α] : IsLeftCancelMulZero (Lex α) := h
instance [Mul α] [Zero α] [h : IsRightCancelMulZero α] : IsRightCancelMulZero (Lex α) := h
instance [Mul α] [Zero α] [h : IsCancelMulZero α] : IsCancelMulZero (Lex α) := h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero (Lex α) := h

instance [h : GroupWithZero α] : GroupWithZero (Lex α) := h

instance [h : CommGroupWithZero α] : CommGroupWithZero (Lex α) := h
