/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

#align_import data.nat.factorial.big_operators from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Factorial with big operators

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `Basic.lean` file, importing
`Algebra.BigOperators.Group.Finset` leads to a cyclic import.

-/


open Finset Nat

namespace Nat

lemma monotone_factorial : Monotone factorial := fun _ _ => factorial_le
#align nat.monotone_factorial Nat.monotone_factorial

variable {α : Type*} (s : Finset α) (f : α → ℕ)

theorem prod_factorial_pos : 0 < ∏ i ∈ s, (f i)! := by positivity
#align nat.prod_factorial_pos Nat.prod_factorial_pos

theorem prod_factorial_dvd_factorial_sum : (∏ i ∈ s, (f i)!) ∣ (∑ i ∈ s, f i)! := by
  induction' s using Finset.cons_induction_on with a s has ih
  · simp
  · rw [prod_cons, Finset.sum_cons]
    exact (mul_dvd_mul_left _ ih).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem descFactorial_eq_prod_range (n : ℕ) : ∀ k, n.descFactorial k = ∏ i ∈ range k, (n - i)
  | 0 => rfl
  | k + 1 => by rw [descFactorial, prod_range_succ, mul_comm, descFactorial_eq_prod_range n k]

end Nat
