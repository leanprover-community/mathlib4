/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Order

#align_import data.nat.factorial.big_operators from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Factorial with big operators

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `Basic.lean` file, importing
`Algebra.BigOperators.Basic` leads to a cyclic import.

-/


open Nat
open BigOperators

namespace Nat

variable {α : Type*} (s : Finset α) (f : α → ℕ)

theorem prod_factorial_pos : 0 < ∏ i in s, (f i)! :=
  Finset.prod_pos fun i _ => factorial_pos (f i)
#align nat.prod_factorial_pos Nat.prod_factorial_pos

theorem prod_factorial_dvd_factorial_sum : (∏ i in s, (f i)!) ∣ (∑ i in s, f i)! := by
  classical
    induction' s using Finset.induction with a' s' has ih
    · simp only [Finset.sum_empty, Finset.prod_empty, factorial]
    · simp only [Finset.prod_insert has, Finset.sum_insert has]
      refine' dvd_trans (mul_dvd_mul_left (f a')! ih) _
      apply Nat.factorial_mul_factorial_dvd_factorial_add
#align nat.prod_factorial_dvd_factorial_sum Nat.prod_factorial_dvd_factorial_sum

end Nat
