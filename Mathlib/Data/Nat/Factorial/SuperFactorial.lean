/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Monic
import Mathlib.LinearAlgebra.Matrix.Block
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

@[simp]
theorem prod_range_succ_factorial : ∀ n : ℕ, ∏ x in range (n + 1), x ! = sf n
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

open Polynomial

theorem eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials {n : ℕ}
    (v : Fin n → R) (p : Fin n → R[X]) (h_deg : ∀ i, (p i).natDegree ≤ i) :
    Matrix.of (fun i j => ((p j).eval (v i))) =
    (Matrix.vandermonde v) * (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) := by
  ext i j
  rw [Matrix.mul_apply, Polynomial.eval, Matrix.of_apply, Polynomial.eval₂]
  simp only [eq_intCast, Int.cast_id, Matrix.vandermonde]
  have : (p j).support ⊆ range n := supp_subset_range <| Nat.lt_of_le_of_lt (h_deg j) <| Fin.prop j
  rw [sum_eq_of_subset _ (fun j => zero_mul ((v i) ^ j)) this, ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, Matrix.of_apply, RingHom.id_apply]

theorem matrixOfPolynomials_blockTriangular {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree ≤ i) :
    Matrix.BlockTriangular (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) id :=
  fun _ j h => by
    refine' coeff_eq_zero_of_natDegree_lt <| Nat.lt_of_le_of_lt (h_deg j) h

theorem det_matrixOfPolynomials {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree = i) (h_monic : ∀ i, Monic <| p i) :
    (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (matrixOfPolynomials_blockTriangular p (fun i ↦
      Nat.le_of_eq (h_deg i)))]
  convert prod_const_one with x _
  rw [Matrix.of_apply, ← h_deg, coeff_natDegree, (h_monic x).leadingCoeff]

theorem det_eval_matrixOfPolynomials_eq_det_vandermonde {n : ℕ} (v : Fin n → R) (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree = i) (h_monic : ∀ i, Monic <| p i) :
    (Matrix.vandermonde v).det = (Matrix.of (fun i j => ((p j).eval (v i)))).det := by
  rw [eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials v p (fun i ↦
      Nat.le_of_eq (h_deg i)), Matrix.det_mul,
      det_matrixOfPolynomials p h_deg h_monic, mul_one]

theorem matrixOf_eval_descPochhammer_eq_mul_matrixOf_choose {n : ℕ} (v : Fin n → ℕ) :
    (Matrix.of (fun (i j : Fin n) => (descPochhammer ℤ j).eval (v i : ℤ))).det =
    (∏ i : Fin n, Nat.factorial i) *
      (Matrix.of (fun (i j : Fin n) => (Nat.choose (v i) (j : ℕ) : ℤ))).det := by
  convert Matrix.det_mul_row (fun (i : Fin n) => ((Nat.factorial (i : ℕ)):ℤ)) _
  · rw [Matrix.of_apply, descPochhammer_int_eq_descFactorial _ _]
    congr
    exact Nat.descFactorial_eq_factorial_mul_choose _ _
  · rw [Nat.cast_prod]

theorem superFactorial_dvd_vandermonde_det {n : ℕ} (v : Fin (n + 1) → ℤ) :
    ↑(Nat.superFactorial n) ∣ (Matrix.vandermonde v).det := by
  let m := inf' univ ⟨0, mem_univ _⟩ v
  let w' := fun i ↦ (v i - m).toNat
  have hw' : ∀ i, (w' i : ℤ) = v i - m := fun i ↦ Int.toNat_sub_of_le (inf'_le _ (mem_univ _))
  have h :=  det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i ↦ ↑(w' i))
      (fun i => descPochhammer ℤ i)
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)
  conv_lhs at h => simp only [hw', Matrix.det_vandermonde_sub]
  use (Matrix.of (fun (i j : Fin (n + 1)) => (Nat.choose (w' i) (j : ℕ) : ℤ))).det
  simp [h, matrixOf_eval_descPochhammer_eq_mul_matrixOf_choose w', Fin.prod_univ_eq_prod_range]

end SuperFactorial

end Nat
