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

variable {α : Type*}


/-! ### Order dual -/


namespace OrderDual

instance [MulZeroClass α] : MulZeroClass αᵒᵈ := inferInstanceAs <| MulZeroClass α

instance [MulZeroOneClass α] : MulZeroOneClass αᵒᵈ := inferInstanceAs <| MulZeroOneClass α

instance [Mul α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors αᵒᵈ :=
  inferInstanceAs <| NoZeroDivisors α

instance [SemigroupWithZero α] : SemigroupWithZero αᵒᵈ := inferInstanceAs <| SemigroupWithZero α

instance [MonoidWithZero α] : MonoidWithZero αᵒᵈ := inferInstanceAs <| MonoidWithZero α

instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero αᵒᵈ :=
  inferInstanceAs <| IsLeftCancelMulZero α

instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero αᵒᵈ :=
  inferInstanceAs <| IsRightCancelMulZero α

instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵒᵈ where

instance [CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ := inferInstanceAs <| CommMonoidWithZero α

instance [GroupWithZero α] : GroupWithZero αᵒᵈ := inferInstanceAs <| GroupWithZero α

instance [CommGroupWithZero α] : CommGroupWithZero αᵒᵈ := inferInstanceAs <| CommGroupWithZero α

end OrderDual

/-! ### Lexicographic order -/


namespace Lex

instance [MulZeroClass α] : MulZeroClass (Lex α) where
  zero_mul _ := Lex.ext (zero_mul _)
  mul_zero _ := Lex.ext (mul_zero _)

instance [MulZeroOneClass α] : MulZeroOneClass (Lex α) where

instance [Mul α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors (Lex α) where
  eq_zero_or_eq_zero_of_mul_eq_zero h := by
    rw [toLex_inj, ofLex_mul] at h
    rw [toLex_inj, toLex_inj]
    exact eq_zero_or_eq_zero_of_mul_eq_zero h

instance [SemigroupWithZero α] : SemigroupWithZero (Lex α) where

instance [MonoidWithZero α] : MonoidWithZero (Lex α) where

instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero (Lex α) where
  mul_left_cancel_of_ne_zero ha _ _ e :=
    Lex.ext (mul_left_cancel₀ (Lex.ext_iff.ne.mp ha) (Lex.ext_iff.mp e))

instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero (Lex α) where
  mul_right_cancel_of_ne_zero ha _ _ e :=
    Lex.ext (mul_right_cancel₀ (Lex.ext_iff.ne.mp ha) (Lex.ext_iff.mp e))

instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero (Lex α) where

instance [CommMonoidWithZero α] : CommMonoidWithZero (Lex α) where

instance [GroupWithZero α] : GroupWithZero (Lex α) where
  inv_zero := Lex.ext inv_zero
  mul_inv_cancel _ h := Lex.ext (mul_inv_cancel₀ (Lex.ext_iff.ne.mp h))

instance [CommGroupWithZero α] : CommGroupWithZero (Lex α) where

end Lex
