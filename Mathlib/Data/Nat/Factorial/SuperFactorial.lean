/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Superfactorial

This file defines the [superfactorial](https://en.wikipedia.org/wiki/Superfactorial)
`sf n = 1! * 2! * 3! * ... * n!`.

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

open Finset

@[simp]
theorem prod_Icc_factorial : ∀ n : ℕ, ∏ x ∈ Icc 1 n, x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [← Ico_add_one_right_eq_Icc 1, prod_Ico_succ_top le_add_self, Nat.factorial_succ,
      Ico_add_one_right_eq_Icc 1 n, prod_Icc_factorial n, superFactorial, factorial, mul_comm]

@[simp]
theorem prod_range_factorial_succ (n : ℕ) : ∏ x ∈ range n, (x + 1)! = sf n :=
  (prod_Icc_factorial n) ▸ range_eq_Ico ▸ Finset.prod_Ico_add' _ _ _ _

@[simp]
theorem prod_range_succ_factorial : ∀ n : ℕ, ∏ x ∈ range (n + 1), x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [prod_range_succ, prod_range_succ_factorial n, mul_comm, superFactorial]

theorem superFactorial_two_mul : ∀ n : ℕ,
    sf (2 * n) = (∏ i ∈ range n, (2 * i + 1) !) ^ 2 * 2 ^ n * n !
  | 0 => rfl
  | (n + 1) => by
    simp only [prod_range_succ, mul_pow, mul_add, mul_one, superFactorial_succ,
      superFactorial_two_mul n, factorial_succ]
    ring

theorem superFactorial_four_mul (n : ℕ) :
    sf (4 * n) = ((∏ i ∈ range (2 * n), (2 * i + 1) !) * 2 ^ n) ^ 2 * (2 * n) ! :=
  calc
    sf (4 * n) = (∏ i ∈ range (2 * n), (2 * i + 1) !) ^ 2 * 2 ^ (2 * n) * (2 * n) ! := by
      rw [← superFactorial_two_mul, ← mul_assoc, Nat.mul_two]
    _ = ((∏ i ∈ range (2 * n), (2 * i + 1) !) * 2 ^ n) ^ 2 * (2 * n) ! := by
      rw [pow_mul', mul_pow]

end SuperFactorial

end Nat
