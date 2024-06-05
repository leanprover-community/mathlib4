/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GeomSum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

#align_import linear_algebra.vandermonde from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.

## Main definitions

 - `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.

## Main results

 - `det_vandermonde`: `det (vandermonde v)` is the product of `v i - v j`, where
   `(i, j)` ranges over the unordered pairs.
-/


variable {R : Type*} [CommRing R]

open Equiv Finset

open Matrix

namespace Matrix

/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`.
-/
def vandermonde {n : ℕ} (v : Fin n → R) : Matrix (Fin n) (Fin n) R := fun i j => v i ^ (j : ℕ)
#align matrix.vandermonde Matrix.vandermonde

@[simp]
theorem vandermonde_apply {n : ℕ} (v : Fin n → R) (i j) : vandermonde v i j = v i ^ (j : ℕ) :=
  rfl
#align matrix.vandermonde_apply Matrix.vandermonde_apply

@[simp]
theorem vandermonde_cons {n : ℕ} (v0 : R) (v : Fin n → R) :
    vandermonde (Fin.cons v0 v : Fin n.succ → R) =
      Fin.cons (fun (j : Fin n.succ) => v0 ^ (j : ℕ)) fun i => Fin.cons 1
      fun j => v i * vandermonde v i j := by
  ext i j
  refine Fin.cases (by simp) (fun i => ?_) i
  refine Fin.cases (by simp) (fun j => ?_) j
  simp [pow_succ']
#align matrix.vandermonde_cons Matrix.vandermonde_cons

theorem vandermonde_succ {n : ℕ} (v : Fin n.succ → R) :
    vandermonde v =
      Fin.cons (fun (j : Fin n.succ) => v 0 ^ (j : ℕ)) fun i =>
        Fin.cons 1 fun j => v i.succ * vandermonde (Fin.tail v) i j := by
  conv_lhs => rw [← Fin.cons_self_tail v, vandermonde_cons]
  rfl
#align matrix.vandermonde_succ Matrix.vandermonde_succ

theorem vandermonde_mul_vandermonde_transpose {n : ℕ} (v w : Fin n → R) (i j) :
    (vandermonde v * (vandermonde w)ᵀ) i j = ∑ k : Fin n, (v i * w j) ^ (k : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_pow]
#align matrix.vandermonde_mul_vandermonde_transpose Matrix.vandermonde_mul_vandermonde_transpose

theorem vandermonde_transpose_mul_vandermonde {n : ℕ} (v : Fin n → R) (i j) :
    ((vandermonde v)ᵀ * vandermonde v) i j = ∑ k : Fin n, v k ^ (i + j : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_add]
#align matrix.vandermonde_transpose_mul_vandermonde Matrix.vandermonde_transpose_mul_vandermonde

theorem det_vandermonde {n : ℕ} (v : Fin n → R) :
    det (vandermonde v) = ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i) := by
  unfold vandermonde
  induction' n with n ih
  · exact det_eq_one_of_card_eq_zero (Fintype.card_fin 0)
  calc
    det (of fun i j : Fin n.succ => v i ^ (j : ℕ)) =
        det
          (of fun i j : Fin n.succ =>
            Matrix.vecCons (v 0 ^ (j : ℕ)) (fun i => v (Fin.succ i) ^ (j : ℕ) - v 0 ^ (j : ℕ)) i) :=
      det_eq_of_forall_row_eq_smul_add_const (Matrix.vecCons 0 1) 0 (Fin.cons_zero _ _) ?_
    _ =
        det
          (of fun i j : Fin n =>
            Matrix.vecCons (v 0 ^ (j.succ : ℕ))
              (fun i : Fin n => v (Fin.succ i) ^ (j.succ : ℕ) - v 0 ^ (j.succ : ℕ))
              (Fin.succAbove 0 i)) := by
      simp_rw [det_succ_column_zero, Fin.sum_univ_succ, of_apply, Matrix.cons_val_zero, submatrix,
        of_apply, Matrix.cons_val_succ, Fin.val_zero, pow_zero, one_mul, sub_self,
        mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    _ =
        det
          (of fun i j : Fin n =>
              (v (Fin.succ i) - v 0) *
                ∑ k ∈ Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :
            Matrix _ _ R) := by
      congr
      ext i j
      rw [Fin.succAbove_zero, Matrix.cons_val_succ, Fin.val_succ, mul_comm]
      exact (geom_sum₂_mul (v i.succ) (v 0) (j + 1 : ℕ)).symm
    _ =
        (∏ i ∈ Finset.univ, (v (Fin.succ i) - v 0)) *
          det fun i j : Fin n =>
            ∑ k ∈ Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :=
      (det_mul_column (fun i => v (Fin.succ i) - v 0) _)
    _ = (∏ i ∈ Finset.univ, (v (Fin.succ i) - v 0)) *
    det fun i j : Fin n => v (Fin.succ i) ^ (j : ℕ) := congr_arg _ ?_
    _ = ∏ i : Fin n.succ, ∏ j ∈ Ioi i, (v j - v i) := by
      simp_rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]
      have h := ih (v ∘ Fin.succ)
      unfold Function.comp at h
      rw [h]

  · intro i j
    simp_rw [of_apply]
    rw [Matrix.cons_val_zero]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    rw [Matrix.cons_val_succ, Matrix.cons_val_succ, Pi.one_apply]
    ring
  · cases n
    · rw [det_eq_one_of_card_eq_zero (Fintype.card_fin 0),
      det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
    apply det_eq_of_forall_col_eq_smul_add_pred fun _ => v 0
    · intro j
      simp
    · intro i j
      simp only [smul_eq_mul, Pi.add_apply, Fin.val_succ, Fin.coe_castSucc, Pi.smul_apply]
      rw [Finset.sum_range_succ, add_comm, tsub_self, pow_zero, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i' hi' => ?_
      rw [mul_left_comm (v 0), Nat.succ_sub, pow_succ']
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
#align matrix.det_vandermonde Matrix.det_vandermonde

theorem det_vandermonde_eq_zero_iff [IsDomain R] {n : ℕ} {v : Fin n → R} :
    det (vandermonde v) = 0 ↔ ∃ i j : Fin n, v i = v j ∧ i ≠ j := by
  constructor
  · simp only [det_vandermonde v, Finset.prod_eq_zero_iff, sub_eq_zero, forall_exists_index]
    rintro i ⟨_, j, h₁, h₂⟩
    exact ⟨j, i, h₂, (mem_Ioi.mp h₁).ne'⟩
  · simp only [Ne, forall_exists_index, and_imp]
    refine fun i j h₁ h₂ => Matrix.det_zero_of_row_eq h₂ (funext fun k => ?_)
    rw [vandermonde_apply, vandermonde_apply, h₁]
#align matrix.det_vandermonde_eq_zero_iff Matrix.det_vandermonde_eq_zero_iff

theorem det_vandermonde_ne_zero_iff [IsDomain R] {n : ℕ} {v : Fin n → R} :
    det (vandermonde v) ≠ 0 ↔ Function.Injective v := by
  unfold Function.Injective
  simp only [det_vandermonde_eq_zero_iff, Ne, not_exists, not_and, Classical.not_not]
#align matrix.det_vandermonde_ne_zero_iff Matrix.det_vandermonde_ne_zero_iff

@[simp]
theorem det_vandermonde_add {n : ℕ} (v : Fin n → R) (a : R) :
    (Matrix.vandermonde fun i ↦ v i + a).det = (Matrix.vandermonde v).det := by
  simp [Matrix.det_vandermonde]

@[simp]
theorem det_vandermonde_sub {n : ℕ} (v : Fin n → R) (a : R) :
    (Matrix.vandermonde fun i ↦ v i - a).det = (Matrix.vandermonde v).det := by
  rw [← det_vandermonde_add v (- a)]
  simp only [← sub_eq_add_neg]

theorem eq_zero_of_forall_index_sum_pow_mul_eq_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f)
    (hfv : ∀ j, (∑ i : Fin n, f j ^ (i : ℕ) * v i) = 0) : v = 0 :=
  eq_zero_of_mulVec_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)
#align matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero

theorem eq_zero_of_forall_index_sum_mul_pow_eq_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f) (hfv : ∀ j, (∑ i, v i * f j ^ (i : ℕ)) = 0) :
    v = 0 := by
  apply eq_zero_of_forall_index_sum_pow_mul_eq_zero hf
  simp_rw [mul_comm]
  exact hfv
#align matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero

theorem eq_zero_of_forall_pow_sum_mul_pow_eq_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f)
    (hfv : ∀ i : Fin n, (∑ j : Fin n, v j * f j ^ (i : ℕ)) = 0) : v = 0 :=
  eq_zero_of_vecMul_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)
#align matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero

open Polynomial

theorem eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials {n : ℕ}
    (v : Fin n → R) (p : Fin n → R[X]) (h_deg : ∀ i, (p i).natDegree ≤ i) :
    Matrix.of (fun i j => ((p j).eval (v i))) =
    (Matrix.vandermonde v) * (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) := by
  ext i j
  rw [Matrix.mul_apply, eval, Matrix.of_apply, eval₂]
  simp only [eq_intCast, Int.cast_id, Matrix.vandermonde]
  have : (p j).support ⊆ range n := supp_subset_range <| Nat.lt_of_le_of_lt (h_deg j) <| Fin.prop j
  rw [sum_eq_of_subset _ (fun j => zero_mul ((v i) ^ j)) this, ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, Matrix.of_apply, RingHom.id_apply]

theorem det_eval_matrixOfPolynomials_eq_det_vandermonde {n : ℕ} (v : Fin n → R) (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree = i) (h_monic : ∀ i, Monic <| p i) :
    (Matrix.vandermonde v).det = (Matrix.of (fun i j => ((p j).eval (v i)))).det := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials v p (fun i ↦
      Nat.le_of_eq (h_deg i)), Matrix.det_mul,
      Matrix.det_matrixOfPolynomials p h_deg h_monic, mul_one]

end Matrix
