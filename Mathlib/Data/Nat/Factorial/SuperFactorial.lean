/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals
/-!
# Superfactorial

This file defines the [superfactorial](https://en.wikipedia.org/wiki/Superfactorial)
`sf n = 1! * 2! * 3! * ...* n!`.

## Main declarations

* `Nat.superFactorial`: The superfactorial, denoted by `sf`.
-/


namespace Nat

/-- `Nat.superFactorial n` is the superfactorial of `n`. -/
def superFactorial : ℕ → ℕ
  | 0 => 1
  | succ n => factorial n.succ * superFactorial n

/-- `sf` notation for superfactorial -/
scoped notation "sf" n:60 => Nat.superFactorial n

section SuperFactorial

variable {n : ℕ}

@[simp]
theorem superFactorial_zero : sf 0 = 1 :=
  rfl

theorem superFactorial_succ (n : ℕ) : (sf n.succ) = (n + 1)! * sf n :=
  rfl

@[simp]
theorem superFactorial_one : sf 1 = 1 :=
  rfl

@[simp]
theorem superFactorial_two : sf 2 = 2 :=
  rfl

open BigOperators Finset

@[simp]
theorem prod_Ico_factorial_eq_superFactorial : ∀ n : ℕ, (∏ x in Ico 1 (n + 1), x !) = sf n
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ico_succ_top <| Nat.succ_le_succ <| Nat.zero_le n, Nat.factorial_succ,
      prod_Ico_factorial_eq_superFactorial n, superFactorial, factorial, Nat.succ_eq_add_one,
      mul_comm]

-- `(x + 1)!` is simplified to `succ x * x!`
@[simp, nolint simpNF]
theorem prod_range_add_one_eq_superFactorial : ∀ n : ℕ, (∏ x in range n, (x + 1) !) = sf n
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ, prod_range_add_one_eq_superFactorial n, superFactorial, mul_comm,
        factorial]

end SuperFactorial

end Nat
