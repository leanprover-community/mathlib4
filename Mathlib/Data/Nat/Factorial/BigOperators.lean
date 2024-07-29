/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

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

theorem descFactorial_eq_prod_range (n : ℕ) : ∀ k, n.descFactorial k = ∏ i ∈ range k, (n - i)
  | 0 => rfl
  | k + 1 => by rw [descFactorial, prod_range_succ, mul_comm, descFactorial_eq_prod_range n k]

lemma exists_descFactorial_eq_polynomial (k : ℕ) : ∃ (a : Fin k → ℕ), ∀ n,
    (n + k).descFactorial k = n ^ k + ∑ i, a i * n ^ (i : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rcases ih with ⟨a, ha⟩
      let b : Fin (k + 1) → ℕ := Fin.cons 0 a
      let c : Fin (k + 1) → ℕ := Fin.snoc (fun i ↦ (k + 1) * a i) (k + 1)
      refine ⟨b + c, fun n ↦ ?_⟩
      calc (n + (k + 1)).descFactorial (k + 1)
      _ = (n + k + 1) * (n + k).descFactorial k := succ_descFactorial_succ (n.add k) k
      _ = (n + (k + 1)) * (n ^ k + ∑ i, a i * n ^ (i : ℕ)) := by rw [add_assoc, ha n]
      _ = n ^ (k + 1) + ∑ i, a i * n ^ ((i : ℕ) + 1)
          + ((k + 1) * n ^ k + ∑ i, (k + 1) * a i * n ^ (i : ℕ)) := by
        rw [add_mul, mul_add, mul_add, _root_.pow_succ', mul_sum, mul_sum]
        congr 3 with i
        · ring
        · ring
      _ = n ^ (k + 1) + ∑ i, b i * n ^ (i : ℕ) + ∑ i, c i * n ^ (i : ℕ) := by
        congr 2
        · simp only [b]
          have I : ∀ (i : Fin (k + 1)), (Fin.cons (α := fun _ ↦ ℕ) (0 : ℕ) a i) * n ^ (i : ℕ)
              = Fin.cons (α := fun _ ↦ ℕ) (0 : ℕ) (fun j ↦ a j * n ^ ((j : ℕ) + 1)) i := by
            apply Fin.cases <;> simp
          simp_rw [I]
          simp [Fin.sum_cons]
        · simp only [c]
          have I : ∀ (i : Fin (k + 1)),
              Fin.snoc (α := fun _ ↦ ℕ) (fun j ↦ (k + 1) * a j) (k + 1) i * n ^ (i : ℕ) =
              Fin.snoc (α := fun _ ↦ ℕ) (fun j ↦ (k + 1) * a j * n ^ (j : ℕ))
                ((k + 1) * n ^ k) i := by
            apply Fin.lastCases <;> simp
          simp_rw [I]
          simp only [Fin.sum_snoc, add_comm]
      _ = n ^ (k + 1) + ∑ i, (b i + c i) * n ^ (i : ℕ) := by
        rw [add_assoc, ← sum_add_distrib]
        congr with i
        rw [add_mul]

end Nat
