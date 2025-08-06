/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Group.Synonym

/-!
# Group with zero structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `Lex α`.
-/


open Function

variable {α : Type*}


/-! ### Order dual -/


open OrderDual

instance [MulZeroClass α] : MulZeroClass αᵒᵈ where
  mul_zero _ := congrArg toDual (mul_zero _)
  zero_mul _ := congrArg toDual (zero_mul _)

instance [MulZeroOneClass α] : MulZeroOneClass αᵒᵈ where
  one_mul _ := congrArg toDual (one_mul _)
  mul_one _ := congrArg toDual (mul_one _)

instance [Mul α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors αᵒᵈ where
  eq_zero_or_eq_zero_of_mul_eq_zero h :=
    (eq_zero_or_eq_zero_of_mul_eq_zero (congrArg ofDual h)).imp (congrArg toDual) (congrArg toDual)

instance [SemigroupWithZero α] : SemigroupWithZero αᵒᵈ where

instance [MonoidWithZero α] : MonoidWithZero αᵒᵈ where

instance [CancelMonoidWithZero α] : CancelMonoidWithZero αᵒᵈ where
  mul_left_cancel_of_ne_zero hzero h :=
    congrArg toDual (mul_left_cancel₀ (hzero ∘ congrArg toDual) (congrArg ofDual h))
  mul_right_cancel_of_ne_zero hzero h :=
    congrArg toDual (mul_right_cancel₀ (hzero ∘ congrArg toDual) (congrArg ofDual h))

instance [CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ where

instance [CancelCommMonoidWithZero α] : CancelCommMonoidWithZero αᵒᵈ where

instance [GroupWithZero α] : GroupWithZero αᵒᵈ where
  inv_zero := congrArg toDual (inv_zero)
  mul_inv_cancel _ h := congrArg toDual (mul_inv_cancel₀ (h ∘ congrArg toDual))

instance [CommGroupWithZero α] : CommGroupWithZero αᵒᵈ where

/-! ### Lexicographic order -/


instance [h : MulZeroClass α] : MulZeroClass (Lex α) := h

instance [h : MulZeroOneClass α] : MulZeroOneClass (Lex α) := h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors (Lex α) := h

instance [h : SemigroupWithZero α] : SemigroupWithZero (Lex α) := h

instance [h : MonoidWithZero α] : MonoidWithZero (Lex α) := h

instance [h : CancelMonoidWithZero α] : CancelMonoidWithZero (Lex α) := h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero (Lex α) := h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero (Lex α) := h

instance [h : GroupWithZero α] : GroupWithZero (Lex α) := h

instance [h : CommGroupWithZero α] : CommGroupWithZero (Lex α) := h
