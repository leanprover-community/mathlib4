/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Factorial with big operators

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `Basic.lean` file, importing
`Algebra.BigOperators.Group.Finset` leads to a cyclic import.

-/


open Finset Nat

namespace Nat

lemma monotone_factorial : Monotone factorial := fun _ _ => factorial_le

variable {α : Type*} (s : Finset α) (f : α → ℕ)

theorem prod_factorial_pos : 0 < ∏ i ∈ s, (f i)! := by positivity

theorem prod_factorial_dvd_factorial_sum : (∏ i ∈ s, (f i)!) ∣ (∑ i ∈ s, f i)! := by
  induction' s using Finset.cons_induction_on with a s has ih
  · simp
  · rw [prod_cons, Finset.sum_cons]
    exact (mul_dvd_mul_left _ ih).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem ascFactorial_eq_prod_range (n : ℕ) : ∀ k, n.ascFactorial k = ∏ i ∈ range k, (n + i)
  | 0 => rfl
  | k + 1 => by rw [ascFactorial, prod_range_succ, mul_comm, ascFactorial_eq_prod_range n k]

theorem descFactorial_eq_prod_range (n : ℕ) : ∀ k, n.descFactorial k = ∏ i ∈ range k, (n - i)
  | 0 => rfl
  | k + 1 => by rw [descFactorial, prod_range_succ, mul_comm, descFactorial_eq_prod_range n k]

end Nat
