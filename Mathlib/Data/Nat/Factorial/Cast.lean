/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.RingTheory.Polynomial.Pochhammer

#align_import data.nat.factorial.cast from "leanprover-community/mathlib"@"d50b12ae8e2bd910d08a94823976adae9825718b"

/-!
# Cast of factorials

This file allows calculating factorials (including ascending and descending ones) as elements of a
semiring.

This is particularly crucial for `Nat.descFactorial` as subtraction on `ℕ` does **not** correspond
to subtraction on a general semiring. For example, we can't rely on existing cast lemmas to prove
`↑(a.descFactorial 2) = ↑a * (↑a - 1)`. We must use the fact that, whenever `↑(a - 1)` is not equal
to `↑a - 1`, the other factor is `0` anyway.
-/


open Nat

variable (S : Type*)

namespace Nat

section Semiring

variable [Semiring S] (a b : ℕ)

-- Porting note: added type ascription around a + 1
theorem cast_ascFactorial : (a.ascFactorial b : S) = (ascPochhammer S b).eval (a : S) := by
  rw [← ascPochhammer_nat_eq_ascFactorial, ascPochhammer_eval_cast]
#align nat.cast_asc_factorial Nat.cast_ascFactorial

-- Porting note: added type ascription around a - (b - 1)
theorem cast_descFactorial :
    (a.descFactorial b : S) = (ascPochhammer S b).eval (a - (b - 1) : S) := by
  rw [← ascPochhammer_eval_cast, ascPochhammer_nat_eq_descFactorial]
  induction' b with b
  · simp
  · simp_rw [add_succ, Nat.add_one_sub_one]
    obtain h | h := le_total a b
    · rw [descFactorial_of_lt (lt_succ_of_le h), descFactorial_of_lt (lt_succ_of_le _)]
      rw [tsub_eq_zero_iff_le.mpr h, zero_add]
    · rw [tsub_add_cancel_of_le h]
#align nat.cast_desc_factorial Nat.cast_descFactorial

theorem cast_factorial : (a ! : S) = (ascPochhammer S a).eval 1 := by
  rw [← one_ascFactorial, cast_ascFactorial, cast_one]
#align nat.cast_factorial Nat.cast_factorial

end Semiring

section Ring

variable [Ring S] (a b : ℕ)

/-- Convenience lemma. The `a - 1` is not using truncated subtraction, as opposed to the definition
of `Nat.descFactorial` as a natural. -/
theorem cast_descFactorial_two : (a.descFactorial 2 : S) = a * (a - 1) := by
  rw [cast_descFactorial]
  cases a
  · simp
  · rw [succ_sub_succ, tsub_zero, cast_succ, add_sub_cancel_right, ascPochhammer_succ_right,
      ascPochhammer_one, Polynomial.X_mul, Polynomial.eval_mul_X, Polynomial.eval_add,
      Polynomial.eval_X, cast_one, Polynomial.eval_one]
#align nat.cast_desc_factorial_two Nat.cast_descFactorial_two

end Ring

end Nat
