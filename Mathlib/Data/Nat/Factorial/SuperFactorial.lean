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

-- TODO: find good place and prove additive/multiplicative version in generality
theorem prod_even_odd (n : ℕ) (f : ℕ → ℕ) :
    ∏ x in Icc 1 (2 * n), f x =  ∏ x in Icc 1 (n), (f (2 * x)) * (f (2 * x - 1)) := by
  induction' n with n hn
  · rfl
  · have h : 2 * succ n = succ (succ (2 * n)) := by rfl
    rw [h, ← Ico_succ_right, prod_Ico_succ_top <| le_add_left 1 (2 * n + 1),
        prod_Ico_succ_top <| le_add_left 1 (2 * n)]
    simp only [← Ico_succ_right, h] at hn
    rw [hn, ← Ico_succ_right, prod_Ico_succ_top <| le_add_left 1 n, succ_eq_add_one, mul_add,
        mul_one, mul_comm (f (2 * n + 2)), mul_assoc]
    rfl

theorem superFactorial_eq_square_times_factorial (k : ℕ) :
    ∃ n, IsSquare n ∧ sf (4 * k) = n * (2 * k) ! := by
  by_cases k = 0
  · exact ⟨1, ⟨isSquare_one, h ▸ rfl⟩⟩
  have hk := Nat.sub_add_cancel <| succ_mul_pos 1 <| Nat.pos_of_ne_zero h
  have h_succ : succ (2 * k - 1) = 2 * k := by linarith
  use (∏ x in Icc 1 (2 * k - 1), x !) * (∏ x in Icc (2*k + 1) (4 * k), x !)
  have h : sf (4 * k) =
      ((∏ x in Icc 1 (2 * k - 1), x !) * (∏ x in Icc (2*k + 1) (4 * k), x !)) * (2 * k) ! := by
    rw [mul_assoc, mul_comm _ (2 * k) !, prod_Icc_factorial, ← mul_assoc, mul_comm _ (2* k)!]
    have := superFactorial_succ (2*k - 1)
    simp only [hk] at this
    rw [← this, ← prod_Icc_factorial, ← prod_Icc_factorial, h_succ]
    have : ∏ i in Ico 1 (4 * k + 1), (fun x ↦ x !) i = ∏ x in Icc 1 (4 * k), x ! := by
      rfl
    rw [← this, ← Finset.prod_Ico_consecutive _ (le_add_left 1 (2 * k)) (by linarith)]
    rfl
  constructor
  · have h' : sf (4 * k) =
       (2 ^ k * ∏ x in Icc 1 (2 * k), (2 * x - 1)!) ^ 2 * (2 * k)! :=
      calc
        sf (4 * k) = ∏ x in Icc 1 (2 * (2 * k)), x ! := by
          rw [←prod_Icc_factorial, ← mul_assoc]
        _ = ∏ x in Icc 1 (2 * k), ((2 * x) !) * ((2 * x - 1)!) := prod_even_odd _ _
        _ = ∏ x in Icc 1 (2 * k), (2 * x) * (2 * x - 1)! ^ 2 := by
          simp only [pow_two, ← mul_assoc]
          apply Finset.prod_congr rfl
          intro x hx
          simp only [mem_Icc] at hx
          have : 0 < 2 * x := by linarith
          rw [← succ_pred_eq_of_pos this]
          rfl
        _ = (2 ^ k) ^ 2 *
            (∏ x in Icc 1 (2 * k), x) * (∏ x in Icc 1 (2 * k), (2 * x - 1)!) ^ 2 := by
          rw [prod_mul_distrib, prod_pow, prod_mul_distrib, pow_eq_prod_const 2]
          simp only [prod_const, card_Icc, add_tsub_cancel_right, card_range]
          rw [mul_comm 2 k, pow_mul]
        _ = (2 ^ k * ∏ x in Icc 1 (2 * k), ((2 * x - 1)!))^2 * (2 * k) ! := by
          rw [mul_assoc, mul_comm (∏ x in Icc 1 (2 * k), x), ← mul_assoc, mul_pow,
              ← prod_Ico_id_eq_factorial (2*k)]
          rfl
    use 2 ^ k * ∏ x in Icc 1 (2 * k), (2 * x - 1)!
    rw [← pow_two]
    rw [h'] at h
    exact (mul_right_cancel₀ (factorial_ne_zero (2 * k)) h).symm
  · exact h

end SuperFactorial

end Nat
