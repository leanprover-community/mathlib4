/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Cast

/-!
# Cast of binomial coefficients

This file allows calculating the binomial coefficient `a.choose b` as an element of a division ring
of characteristic `0`.
-/


open Nat

variable (K : Type*)

namespace Nat
section DivisionSemiring
variable [DivisionSemiring K] [CharZero K]

theorem cast_choose {a b : ℕ} (h : a ≤ b) : (b.choose a : K) = b ! / (a ! * (b - a)!) := by
  have : ∀ {n : ℕ}, (n ! : K) ≠ 0 := Nat.cast_ne_zero.2 (factorial_pos _).ne'
  rw [eq_div_iff_mul_eq (mul_ne_zero this this)]
  rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h]

theorem cast_add_choose {a b : ℕ} : ((a + b).choose a : K) = (a + b)! / (a ! * b !) := by
  rw [cast_choose K (le_add_right _ _), Nat.add_sub_cancel_left]

end DivisionSemiring

section DivisionRing
variable [DivisionRing K] [NeZero (2 : K)]

theorem cast_choose_two (a : ℕ) : (a.choose 2 : K) = a * (a - 1) / 2 := by
  rw [← cast_descFactorial_two, descFactorial_eq_factorial_mul_choose, factorial_two, mul_comm,
    cast_mul, cast_two, eq_div_iff_mul_eq two_ne_zero]

end DivisionRing
end Nat
