/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.nat.factorial.cast
! leanprover-community/mathlib commit d50b12ae8e2bd910d08a94823976adae9825718b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Polynomial.Pochhammer

/-!
# Cast of factorials

This file allows calculating factorials (including ascending and descending ones) as elements of a
semiring.

This is particularly crucial for `nat.desc_factorial` as subtraction on `ℕ` does **not** correspond
to subtraction on a general semiring. For example, we can't rely on existing cast lemmas to prove
`↑(a.desc_factorial 2) = ↑a * (↑a - 1)`. We must use the fact that, whenever `↑(a - 1)` is not equal
to `↑a - 1`, the other factor is `0` anyway.
-/


open Nat

variable (S : Type _)

namespace Nat

section Semiring

variable [Semiring S] (a b : ℕ)

theorem cast_ascFactorial : (a.ascFactorial b : S) = (pochhammer S b).eval (a + 1) := by
  rw [← pochhammer_nat_eq_ascFactorial, pochhammer_eval_cast, Nat.cast_add, Nat.cast_one]
#align nat.cast_asc_factorial Nat.cast_ascFactorial

theorem cast_descFactorial : (a.descFactorial b : S) = (pochhammer S b).eval (a - (b - 1) : ℕ) :=
  by
  rw [← pochhammer_eval_cast, pochhammer_nat_eq_descFactorial]
  cases b
  · simp_rw [desc_factorial_zero]
  simp_rw [add_succ, succ_sub_one]
  obtain h | h := le_total a b
  · rw [desc_factorial_of_lt (lt_succ_of_le h), desc_factorial_of_lt (lt_succ_of_le _)]
    rw [tsub_eq_zero_iff_le.mpr h, zero_add]
  · rw [tsub_add_cancel_of_le h]
#align nat.cast_desc_factorial Nat.cast_descFactorial

theorem cast_factorial : (a ! : S) = (pochhammer S a).eval 1 := by
  rw [← zero_asc_factorial, cast_asc_factorial, cast_zero, zero_add]
#align nat.cast_factorial Nat.cast_factorial

end Semiring

section Ring

variable [Ring S] (a b : ℕ)

/-- Convenience lemma. The `a - 1` is not using truncated subtraction, as opposed to the definition
of `nat.desc_factorial` as a natural. -/
theorem cast_descFactorial_two : (a.descFactorial 2 : S) = a * (a - 1) :=
  by
  rw [cast_desc_factorial]
  cases a
  · rw [zero_tsub, cast_zero, pochhammer_ne_zero_eval_zero _ two_ne_zero, zero_mul]
  ·
    rw [succ_sub_succ, tsub_zero, cast_succ, add_sub_cancel, pochhammer_succ_right, pochhammer_one,
      Polynomial.X_mul, Polynomial.eval_mul_X, Polynomial.eval_add, Polynomial.eval_X, cast_one,
      Polynomial.eval_one]
#align nat.cast_desc_factorial_two Nat.cast_descFactorial_two

end Ring

end Nat

