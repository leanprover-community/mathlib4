/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Vandermonde

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
theorem prod_Icc_factorial : ∀ n : ℕ, ∏ x in Icc 1 n, x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [← Ico_succ_right 1 n.succ, prod_Ico_succ_top <| Nat.succ_le_succ <| Nat.zero_le n,
    Nat.factorial_succ, Ico_succ_right 1 n, prod_Icc_factorial n, superFactorial, factorial,
    Nat.succ_eq_add_one, mul_comm]

@[simp]
theorem prod_range_factorial_succ : ∀ n : ℕ, ∏ x in range n, (x + 1)! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ, prod_range_factorial_succ n, superFactorial, mul_comm, factorial]

variable {R : Type*} [CommRing R]

theorem det_vandermonde_id_eq_superFactorial (n : ℕ) :
    (Matrix.vandermonde (fun (i : Fin (n + 1)) ↦ (i : R))).det = Nat.superFactorial n := by
  induction' n with n hn
  · simp [Matrix.det_vandermonde]
  · rw [Nat.superFactorial, Matrix.det_vandermonde, Fin.prod_univ_succAbove _ 0]
    push_cast
    congr
    · simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
      norm_cast
      simp [Fin.prod_univ_eq_prod_range (fun i ↦ (↑i + 1)) (n + 1)]
    · rw [Matrix.det_vandermonde] at hn
      simp [hn]

end SuperFactorial

end Nat
