/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Group.Synonym

#align_import algebra.group_with_zero.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Group with zero structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `Lex α`.
-/


open scoped Classical

open Function

variable {α : Type*}


/-! ### Order dual -/


open OrderDual

instance [h : MulZeroClass α] : MulZeroClass αᵒᵈ := h

instance [h : MulZeroOneClass α] : MulZeroOneClass αᵒᵈ := h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors αᵒᵈ := h

instance [h : SemigroupWithZero α] : SemigroupWithZero αᵒᵈ := h

instance [h : MonoidWithZero α] : MonoidWithZero αᵒᵈ := h

instance [h : CancelMonoidWithZero α] : CancelMonoidWithZero αᵒᵈ := h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ := h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero αᵒᵈ := h

instance [h : GroupWithZero α] : GroupWithZero αᵒᵈ := h

instance [h : CommGroupWithZero α] : CommGroupWithZero αᵒᵈ := h

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
