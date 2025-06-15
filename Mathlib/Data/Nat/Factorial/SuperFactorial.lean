/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer

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

private theorem matrixOf_eval_descPochhammer_eq_mul_matrixOf_choose {n : ℕ} (v : Fin n → ℕ) :
    (Matrix.of (fun (i j : Fin n) => (descPochhammer ℤ j).eval (v i : ℤ))).det =
    (∏ i : Fin n, Nat.factorial i) *
      (Matrix.of (fun (i j : Fin n) => (Nat.choose (v i) (j : ℕ) : ℤ))).det := by
  convert Matrix.det_mul_row (fun (i : Fin n) => ((Nat.factorial (i : ℕ)) : ℤ)) _
  · rw [Matrix.of_apply, descPochhammer_eval_eq_descFactorial ℤ _ _]
    congr
    exact Nat.descFactorial_eq_factorial_mul_choose _ _
  · rw [Nat.cast_prod]

theorem superFactorial_dvd_vandermonde_det {n : ℕ} (v : Fin (n + 1) → ℤ) :
    ↑(Nat.superFactorial n) ∣ (Matrix.vandermonde v).det := by
  let m := inf' univ ⟨0, mem_univ _⟩ v
  let w' := fun i ↦ (v i - m).toNat
  have hw' : ∀ i, (w' i : ℤ) = v i - m := fun i ↦ Int.toNat_sub_of_le (inf'_le _ (mem_univ _))
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i ↦ ↑(w' i))
      (fun i => descPochhammer ℤ i)
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)
  conv_lhs at h => simp only [hw', Matrix.det_vandermonde_sub]
  use (Matrix.of (fun (i j : Fin (n + 1)) => (Nat.choose (w' i) (j : ℕ) : ℤ))).det
  simp [h, matrixOf_eval_descPochhammer_eq_mul_matrixOf_choose w', Fin.prod_univ_eq_prod_range]

end SuperFactorial

end Nat
