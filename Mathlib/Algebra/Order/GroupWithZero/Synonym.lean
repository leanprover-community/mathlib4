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

@[expose] public section


open Function

variable {α : Type*}


/-! ### Order dual -/


open OrderDual

instance [h : MulZeroClass α] : MulZeroClass αᵒᵈ := h

instance [h : MulZeroOneClass α] : MulZeroOneClass αᵒᵈ := h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors αᵒᵈ := h

instance [h : SemigroupWithZero α] : SemigroupWithZero αᵒᵈ := h

instance [h : MonoidWithZero α] : MonoidWithZero αᵒᵈ := h

instance [Mul α] [Zero α] [h : IsLeftCancelMulZero α] : IsLeftCancelMulZero αᵒᵈ := h
instance [Mul α] [Zero α] [h : IsRightCancelMulZero α] : IsRightCancelMulZero αᵒᵈ := h
instance [Mul α] [Zero α] [h : IsCancelMulZero α] : IsCancelMulZero αᵒᵈ := h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ := h

instance [h : GroupWithZero α] : GroupWithZero αᵒᵈ := h

instance [h : CommGroupWithZero α] : CommGroupWithZero αᵒᵈ := h

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
