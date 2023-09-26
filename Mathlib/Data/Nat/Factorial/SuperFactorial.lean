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
    rw [Finset.prod_range_succ, prod_range_succ_factorial n, superFactorial, mul_comm, factorial]

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
    (v : Fin n → R) (p : Fin n → R[X]) (h_deg : ∀ i, (p i).natDegree = i) :
    Matrix.of (fun i j => ((p j).eval (v i))) =
    (Matrix.vandermonde v) * (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) := by
  ext i j
  rw [Matrix.mul_apply, Polynomial.eval, Matrix.of_apply, Polynomial.eval₂]
  simp only [eq_intCast, Int.cast_id, Matrix.vandermonde]
  have : (p j).support ⊆ range n := supp_subset_range <| h_deg j ▸ Fin.prop j
  rw [sum_eq_of_subset _ (fun j => zero_mul ((v i) ^ j)) this, ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, Matrix.of_apply, RingHom.id_apply]

theorem matrixOfPolynomials_blockTriangular {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree  = i) :
    Matrix.BlockTriangular (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) id :=
  fun _ j h => coeff_eq_zero_of_natDegree_lt (h_deg j ▸ h)

theorem det_matrixOfPolynomials {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree  = i) (h_monic : ∀ i,  Monic <| p i) :
    (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (matrixOfPolynomials_blockTriangular p h_deg)]
  convert prod_const_one
  rw [Matrix.of_apply]
  rename_i x _
  convert h_monic x
  unfold Monic leadingCoeff
  rw [h_deg x]

theorem vandermonde_det_eq_eval_matrixOfPolynomials_det {n : ℕ} (v : Fin n → R) (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree  = i) (h_monic : ∀ i,  Monic <| p i) :
    (Matrix.vandermonde v).det = (Matrix.of (fun i j => ((p j).eval (v i)))).det := by
  rw [eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials v p h_deg, Matrix.det_mul,
      det_matrixOfPolynomials p h_deg h_monic, mul_one]

theorem eval_matrixOfPolynomials_eq_mul_matrix_of_choose {n : ℕ} (v : Fin n → ℕ) :
    (Matrix.of (fun (i j : Fin n) =>
    ((fun n => descPochhammer ℤ n) j).eval ((fun k => (v k : ℤ)) i)) ).det =
    (∏ i : Fin n,  Nat.factorial i) *
    (Matrix.of (fun (i j : Fin n)  => ((Nat.choose ((v i)) (j : ℕ)) : ℤ))).det := by
  convert Matrix.det_mul_row (fun (i : Fin n)  => ((Nat.factorial (i : ℕ)):ℤ)) _
  · rw [Matrix.of_apply, descPochhammer_int_eq_descFactorial _ _]
    congr
    exact Nat.descFactorial_eq_factorial_mul_choose _ _
  · rw [Nat.cast_prod]

theorem superFactorial_dvd_vandermonde_det {n : ℕ} (v : Fin (n + 1) → ℤ) :
   ↑(Nat.superFactorial n) ∣ (Matrix.vandermonde v).det := by
  let m' := List.minimum ((univ : Finset (Fin (n + 1))).image v).toList
  have : ((univ : Finset (Fin (n + 1))).image v).toList ≠ List.nil := by
    simp only [ne_eq, toList_eq_nil, image_eq_empty]
    refine Nonempty.ne_empty univ_nonempty
  cases' Option.isSome_iff_exists.mp <| Option.ne_none_iff_isSome.mp <|
      List.minimum_ne_top_of_ne_nil this with m hm
  have h_min : ∀  l, l ∈ ((univ : Finset (Fin (n + 1))).image v).toList →  m' ≤ l := by
     exact fun l a ↦ List.minimum_le_of_mem' a
  let w' := fun i ↦ (v i - m).toNat
  have h1 := eval_matrixOfPolynomials_eq_mul_matrix_of_choose w'
  rw [← prod_range_succ_factorial, ← Fin.prod_univ_eq_prod_range]
  have h2 := vandermonde_det_eq_eval_matrixOfPolynomials_det (fun i ↦ ↑(w' i))
      (fun i => descPochhammer ℤ i)
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)
  rw [← h2] at h1
  have : Matrix.det (Matrix.vandermonde fun i ↦ ↑(w' i)) = (Matrix.vandermonde v).det := by
    rw [← Matrix.det_vandermonde_sub v m]
    congr
    unfold Matrix.vandermonde
    ext i j
    congr
    simp only [sub_nonneg]
    have : m ≤ v i  := by
      have v_in : (v i) ∈ (image v univ) := by
        unfold Finset.image
        simp only [Multiset.mem_toFinset, Multiset.mem_map, mem_val, mem_univ, true_and,
            exists_apply_eq_apply]
      have  v_in' : ↑(v i) ∈ toList (image v univ) := mem_toList.mpr v_in
      have h_min := h_min (v i) v_in'
      simp only [hm] at h_min
      rw [WithTop.some_eq_coe] at h_min
      norm_num at h_min
      exact h_min
    exact Int.toNat_sub_of_le this
  rw [this] at h1
  norm_num at h1
  use (Matrix.of (fun (i j : Fin (n + 1))  => ((Nat.choose ((v i  - m).toNat) (j : ℕ)) : ℤ))).det
  convert h1
  norm_cast

end SuperFactorial

end Nat
