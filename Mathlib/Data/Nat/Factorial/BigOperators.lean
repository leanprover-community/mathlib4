/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Zify

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

theorem prod_factorial_pos : 0 < ∏ i ∈ s, (f i)! := prod_pos fun _ _ ↦ factorial_pos _

theorem prod_factorial_dvd_factorial_sum : (∏ i ∈ s, (f i)!) ∣ (∑ i ∈ s, f i)! := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [prod_cons, Finset.sum_cons]
    exact (mul_dvd_mul_left _ ih).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem factorial_eq_prod_range_add_one : ∀ n, (n)! = ∏ i ∈ range n, (i + 1)
  | 0 => rfl
  | n + 1 => by rw [factorial, prod_range_succ_comm, factorial_eq_prod_range_add_one n]

@[simp]
theorem _root_.Finset.prod_range_add_one_eq_factorial (n : ℕ) : ∏ i ∈ range n, (i + 1) = (n)! :=
  factorial_eq_prod_range_add_one _ |>.symm

theorem ascFactorial_eq_prod_range (n : ℕ) : ∀ k, n.ascFactorial k = ∏ i ∈ range k, (n + i)
  | 0 => rfl
  | k + 1 => by rw [ascFactorial, prod_range_succ_comm, ascFactorial_eq_prod_range n k]

theorem descFactorial_eq_prod_range (n : ℕ) : ∀ k, n.descFactorial k = ∏ i ∈ range k, (n - i)
  | 0 => rfl
  | k + 1 => by rw [descFactorial, prod_range_succ_comm, descFactorial_eq_prod_range n k]

/-- `k!` divides the product of any `k` consecutive integers. -/
lemma factorial_coe_dvd_prod (k : ℕ) (n : ℤ) : (k ! : ℤ) ∣ ∏ i ∈ range k, (n + i) := by
  rw [Int.dvd_iff_emod_eq_zero, Finset.prod_int_mod]
  simp_rw [← Int.emod_add_emod n]
  have hn : 0 ≤ n % k ! := Int.emod_nonneg n <| Int.natCast_ne_zero.mpr k.factorial_ne_zero
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le hn
  have hdivk := x.factorial_dvd_ascFactorial k
  zify [x.ascFactorial_eq_prod_range k] at hdivk
  rwa [← Finset.prod_int_mod, ← Int.dvd_iff_emod_eq_zero, hx]

end Nat
