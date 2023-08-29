/-
Copyright (c) 2023 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic.Ring

#align_import data.nat.factorial.double_factorial from "leanprover-community/mathlib"@"7daeaf3072304c498b653628add84a88d0e78767"

/-!
# Double factorials

This file defines the double factorial,
  `n‼ := n * (n - 2) * (n - 4) * ...`.

## Main declarations

* `Nat.doubleFactorial`: The double factorial.
-/


open Nat

namespace Nat

/-- `Nat.doubleFactorial n` is the double factorial of `n`. -/
@[simp]
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => (k + 2) * doubleFactorial k
#align nat.double_factorial Nat.doubleFactorial

-- This notation is `\!!` not two !'s
scoped notation:10000 n "‼" => Nat.doubleFactorial n

theorem doubleFactorial_add_two (n : ℕ) : (n + 2)‼ = (n + 2) * n‼ :=
  rfl
#align nat.double_factorial_add_two Nat.doubleFactorial_add_two

theorem doubleFactorial_add_one (n : ℕ) : (n + 1)‼ = (n + 1) * (n - 1)‼ := by cases n <;> rfl
                                                                              -- ⊢ (zero + 1)‼ = (zero + 1) * (zero - 1)‼
                                                                                          -- 🎉 no goals
                                                                                          -- 🎉 no goals
#align nat.double_factorial_add_one Nat.doubleFactorial_add_one

theorem factorial_eq_mul_doubleFactorial : ∀ n : ℕ, (n + 1)! = (n + 1)‼ * n‼
  | 0 => rfl
  | k + 1 => by
    rw [doubleFactorial_add_two, factorial, factorial_eq_mul_doubleFactorial _, mul_comm _ k‼,
      mul_assoc]
#align nat.factorial_eq_mul_double_factorial Nat.factorial_eq_mul_doubleFactorial

theorem doubleFactorial_two_mul : ∀ n : ℕ, (2 * n)‼ = 2 ^ n * n !
  | 0 => rfl
  | n + 1 => by
    rw [mul_add, mul_one, doubleFactorial_add_two, factorial, pow_succ, doubleFactorial_two_mul _,
      succ_eq_add_one]
    ring
    -- 🎉 no goals
#align nat.double_factorial_two_mul Nat.doubleFactorial_two_mul

open BigOperators

theorem doubleFactorial_eq_prod_even : ∀ n : ℕ, (2 * n)‼ = ∏ i in Finset.range n, 2 * (i + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ, ← doubleFactorial_eq_prod_even _, mul_comm (2 * n)‼,
      (by ring : 2 * (n + 1) = 2 * n + 2)]
    rfl
    -- 🎉 no goals
#align nat.double_factorial_eq_prod_even Nat.doubleFactorial_eq_prod_even

theorem doubleFactorial_eq_prod_odd :
    ∀ n : ℕ, (2 * n + 1)‼ = ∏ i in Finset.range n, (2 * (i + 1) + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ, ← doubleFactorial_eq_prod_odd _, mul_comm (2 * n + 1)‼,
      (by ring : 2 * (n + 1) + 1 = 2 * n + 1 + 2)]
    rfl
    -- 🎉 no goals
#align nat.double_factorial_eq_prod_odd Nat.doubleFactorial_eq_prod_odd

end Nat
