/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Invertible.Defs
import Mathlib.Algebra.GroupWithZero.NeZero

#align_import algebra.invertible from "leanprover-community/mathlib"@"722b3b152ddd5e0cf21c0a29787c76596cb6b422"
/-!
# Theorems about invertible elements in a `GroupWithZero`

We intentionally keep imports minimal here as this file is used by `Mathlib.Tactic.NormNum`.
-/

set_option autoImplicit true

universe u

variable {α : Type u}

theorem nonzero_of_invertible [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 :=
  fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟ a * a := by simp [ha]
      _ = 1 := invOf_mul_self a
#align nonzero_of_invertible nonzero_of_invertible

instance (priority := 100) Invertible.ne_zero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨nonzero_of_invertible a⟩
#align invertible.ne_zero Invertible.ne_zero

section GroupWithZero

variable [GroupWithZero α]

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel h, mul_inv_cancel h⟩
#align invertible_of_nonzero invertibleOfNonzero

@[simp]
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel (nonzero_of_invertible a))
#align inv_of_eq_inv invOf_eq_inv

@[simp]
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel (nonzero_of_invertible a)
#align inv_mul_cancel_of_invertible inv_mul_cancel_of_invertible

@[simp]
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  mul_inv_cancel (nonzero_of_invertible a)
#align mul_inv_cancel_of_invertible mul_inv_cancel_of_invertible

/-- `a` is the inverse of `a⁻¹` -/
def invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩
#align invertible_inv invertibleInv

end GroupWithZero
