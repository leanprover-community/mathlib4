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

instance [MulZeroClass α] : MulZeroClass αᵒᵈ where
  zero_mul _ := by rw [toDual_inj]; exact zero_mul _
  mul_zero _ := by rw [toDual_inj]; exact mul_zero _

instance [MulZeroOneClass α] : MulZeroOneClass αᵒᵈ where

instance [Mul α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors αᵒᵈ where
  eq_zero_or_eq_zero_of_mul_eq_zero h := by
    rw [toDual_inj, ofDual_mul] at h
    rw [toDual_inj, toDual_inj]
    exact eq_zero_or_eq_zero_of_mul_eq_zero h

instance [SemigroupWithZero α] : SemigroupWithZero αᵒᵈ where

instance [MonoidWithZero α] : MonoidWithZero αᵒᵈ where

instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero αᵒᵈ where
  mul_left_cancel_of_ne_zero {a} ha x y e := by
    replace ha : ofDual a ≠ 0 := fun hc ↦ ha (ofDual_inj.mp hc)
    rw [toDual_inj] at e ⊢
    exact mul_left_cancel₀ ha e

instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero αᵒᵈ where
  mul_right_cancel_of_ne_zero {a} ha x y e := by
    replace ha : ofDual a ≠ 0 := fun hc ↦ ha (ofDual_inj.mp hc)
    rw [toDual_inj] at e ⊢
    exact mul_right_cancel₀ ha e

instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵒᵈ where

instance [CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ where

instance [GroupWithZero α] : GroupWithZero αᵒᵈ where
  inv_zero := by rw [toDual_inj]; simp
  mul_inv_cancel a ha := by
    replace ha : ofDual a ≠ 0 := fun hc ↦ ha (ofDual_inj.mp hc)
    rw [toDual_inj]
    exact mul_inv_cancel₀ ha

instance [CommGroupWithZero α] : CommGroupWithZero αᵒᵈ where

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
