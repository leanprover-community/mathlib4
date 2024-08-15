/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Theorems about invertible elements in a `GroupWithZero`

We intentionally keep imports minimal here as this file is used by `Mathlib.Tactic.NormNum`.
-/

assert_not_exists DenselyOrdered

universe u

variable {α : Type u}

theorem nonzero_of_invertible [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 :=
  fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟ a * a := by simp [ha]
      _ = 1 := invOf_mul_self a

instance (priority := 100) Invertible.ne_zero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨nonzero_of_invertible a⟩

section MonoidWithZero
variable [MonoidWithZero α]

/-- A variant of `Ring.inverse_unit`. -/
@[simp]
theorem Ring.inverse_invertible (x : α) [Invertible x] : Ring.inverse x = ⅟ x :=
  Ring.inverse_unit (unitOfInvertible _)

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero α]

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel h, mul_inv_cancel h⟩

@[simp]
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel (nonzero_of_invertible a))

@[simp]
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel (nonzero_of_invertible a)

@[simp]
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  mul_inv_cancel (nonzero_of_invertible a)

/-- `a` is the inverse of `a⁻¹` -/
def invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩

@[simp]
theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel₀ a (nonzero_of_invertible b)

@[simp]
theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  mul_div_cancel_right₀ a (nonzero_of_invertible b)

@[simp]
theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  div_self (nonzero_of_invertible a)

/-- `b / a` is the inverse of `a / b` -/
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩

-- Porting note (#10618): removed `simp` attribute as `simp` can prove it
theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟ (a / b) = b / a :=
  invOf_eq_right_inv (by simp [← mul_div_assoc])

end GroupWithZero
