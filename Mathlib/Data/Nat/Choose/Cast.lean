/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.nat.choose.cast
! leanprover-community/mathlib commit bb168510ef455e9280a152e7f31673cabd3d7496
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Cast

/-!
# Cast of binomial coefficients

This file allows calculating the binomial coefficient `a.choose b` as an element of a division ring
of characteristic `0`.
-/


open Nat

variable (K : Type _) [DivisionRing K] [CharZero K]

namespace Nat

theorem cast_choose {a b : ℕ} (h : a ≤ b) : (b.choose a : K) = b ! / (a ! * (b - a)!) := by
  have : ∀ {n : ℕ}, (n ! : K) ≠ 0 := by simp [cast_ne_zero, factorial_ne_zero]
  rw [eq_div_iff_mul_eq (mul_ne_zero this this)]
  rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h]
#align nat.cast_choose Nat.cast_choose

theorem cast_add_choose {a b : ℕ} : ((a + b).choose a : K) = (a + b)! / (a ! * b !) := by
  rw [cast_choose]
  · rw [add_tsub_cancel_left]
  · simp
#align nat.cast_add_choose Nat.cast_add_choose

theorem cast_choose_eq_pochhammer_div (a b : ℕ) :
    (a.choose b : K) = (pochhammer K b).eval ↑(a - (b - 1)) / b ! := by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) ≠ 0), ← cast_mul,
    mul_comm, ← descFactorial_eq_factorial_mul_choose, ← cast_descFactorial]
#align nat.cast_choose_eq_pochhammer_div Nat.cast_choose_eq_pochhammer_div

theorem cast_choose_two (a : ℕ) : (a.choose 2 : K) = a * (a - 1) / 2 := by
  rw [← cast_descFactorial_two, descFactorial_eq_factorial_mul_choose, factorial_two, mul_comm,
    cast_mul, cast_two, eq_div_iff_mul_eq (two_ne_zero : (2 : K) ≠ 0)]
#align nat.cast_choose_two Nat.cast_choose_two

end Nat
