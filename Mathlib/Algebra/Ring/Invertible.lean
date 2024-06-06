/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Ring.Defs

#align_import algebra.invertible from "leanprover-community/mathlib"@"722b3b152ddd5e0cf21c0a29787c76596cb6b422"
/-!
# Theorems about invertible elements in rings

-/

universe u

variable {α : Type u}

/-- `-⅟a` is the inverse of `-a` -/
def invertibleNeg [Mul α] [One α] [HasDistribNeg α] (a : α) [Invertible a] : Invertible (-a) :=
  ⟨-⅟ a, by simp, by simp⟩
#align invertible_neg invertibleNeg

@[simp]
theorem invOf_neg [Monoid α] [HasDistribNeg α] (a : α) [Invertible a] [Invertible (-a)] :
    ⅟ (-a) = -⅟ a :=
  invOf_eq_right_inv (by simp)
#align inv_of_neg invOf_neg

@[simp]
theorem one_sub_invOf_two [Ring α] [Invertible (2 : α)] : 1 - (⅟ 2 : α) = ⅟ 2 :=
  (isUnit_of_invertible (2 : α)).mul_right_inj.1 <| by
    rw [mul_sub, mul_invOf_self, mul_one, ← one_add_one_eq_two, add_sub_cancel_right]
#align one_sub_inv_of_two one_sub_invOf_two

@[simp]
theorem invOf_two_add_invOf_two [NonAssocSemiring α] [Invertible (2 : α)] :
    (⅟ 2 : α) + (⅟ 2 : α) = 1 := by rw [← two_mul, mul_invOf_self]
#align inv_of_two_add_inv_of_two invOf_two_add_invOf_two

theorem pos_of_invertible_cast [Semiring α] [Nontrivial α] (n : ℕ) [Invertible (n : α)] : 0 < n :=
  Nat.zero_lt_of_ne_zero fun h => nonzero_of_invertible (n : α) (h ▸ Nat.cast_zero)
