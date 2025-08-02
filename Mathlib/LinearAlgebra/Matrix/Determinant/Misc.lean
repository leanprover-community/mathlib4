/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.NegOnePow

/-!
# Miscellaneous results about determinant

In this file, we collect various formulas about determinant of matrices.
-/

assert_not_exists TwoSidedIdeal

namespace Matrix

variable {R : Type*} [CommRing R]

/-- Let `M` be a `(n+1) × n` matrix whose row sums to zero. Then all the matrices obtained by
deleting one row have the same determinant up to a sign. -/
theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin n) R) (hv : ∑ j, M j = 0) (j₁ j₂ : Fin (n + 1)) :
    (M.submatrix (Fin.succAbove j₁) id).det =
      Int.negOnePow (j₁ - j₂) • (M.submatrix (Fin.succAbove j₂) id).det := by
  suffices ∀ j, (M.submatrix (Fin.succAbove j) id).det =
      Int.negOnePow j • (M.submatrix (Fin.succAbove 0) id).det by
    rw [this j₁, this j₂, smul_smul, ← Int.negOnePow_add, sub_add_cancel]
  intro j
  induction j using Fin.induction with
  | zero => rw [Fin.val_zero, Nat.cast_zero, Int.negOnePow_zero, one_smul]
  | succ i h_ind =>
      rw [Fin.val_succ, Nat.cast_add, Nat.cast_one, Int.negOnePow_succ, Units.neg_smul,
        ← neg_eq_iff_eq_neg, ← neg_one_smul R,
        ← det_updateRow_sum (M.submatrix i.succ.succAbove id) i (fun _ ↦ -1),
        ← Fin.coe_castSucc i, ← h_ind]
      congr
      ext a b
      simp_rw [neg_one_smul, updateRow_apply, Finset.sum_neg_distrib, Pi.neg_apply,
        Finset.sum_apply, submatrix_apply, id_eq]
      split_ifs with h
      · replace hv := congr_fun hv b
        rw [Fin.sum_univ_succAbove _ i.succ, Pi.add_apply, Finset.sum_apply] at hv
        rwa [h, Fin.succAbove_castSucc_self, neg_eq_iff_add_eq_zero, add_comm]
      · obtain h|h := ne_iff_lt_or_gt.mp h
        · rw [Fin.succAbove_castSucc_of_lt _ _ h,
            Fin.succAbove_of_succ_le _ _ (Fin.succ_lt_succ_iff.mpr h).le]
        · rw [Fin.succAbove_succ_of_lt _ _ h, Fin.succAbove_castSucc_of_le _ _ h.le]

/-- Let `M` be a `(n+1) × n` matrix whose column sums to zero. Then all the matrices obtained by
deleting one column have the same determinant up to a sign. -/
theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det' {n : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) R) (hv : ∀ i, ∑ j, M i j = 0) (j₁ j₂ : Fin (n + 1)) :
    (M.submatrix id (Fin.succAbove j₁)).det =
      Int.negOnePow (j₁ - j₂) • (M.submatrix id (Fin.succAbove j₂)).det := by
  rw [← det_transpose, transpose_submatrix,
    submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det M.transpose ?_ j₁ j₂,
    ← det_transpose, transpose_submatrix, transpose_transpose]
  ext
  simp_rw [Finset.sum_apply, transpose_apply, hv, Pi.zero_apply]

/-- Let `M` be a `(n+1) × (n+1)` matrix. Assume that all columns, but the `j₀`-column, sums to zero.
Then its determinant is, up to sign, the sum of the `j₀`-column times the determinant of the
matrix obtained by deleting any row and the `j₀`-column. -/
theorem det_eq_sum_column_mul_submatrix_succAbove_succAbove_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1))
    (hv : ∀ j ≠ j₀, ∑ i, M i j = 0) :
    M.det = (-1) ^ (i₀ + j₀ : ℕ) *
      (∑ i, M i j₀) * (M.submatrix (Fin.succAbove i₀) (Fin.succAbove j₀)).det := by
  rw [← one_smul R M.det, ← Matrix.det_updateRow_sum _ i₀ (fun _ ↦ 1), Matrix.det_succ_row _ i₀]
  simp only [updateRow_apply, if_true, one_smul, submatrix_updateRow_succAbove, Finset.sum_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀]
  conv_lhs =>
    enter [2, 2, i]
    rw [hv _ i.prop, mul_zero, zero_mul]
  simp [Finset.sum_const_zero, add_zero]

/-- Let `M` be a `(n+1) × (n+1)` matrix. Assume that all rows, but the `i₀`-row, sums to zero.
Then its determinant is, up to sign, the sum of the `i₀`-row times the determinant of the
matrix obtained by deleting the `i₀`-row and any column. -/
theorem det_eq_sum_row_mul_submatrix_succAbove_succAbove_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1))
    (hv : ∀ i ≠ i₀, ∑ j, M i j = 0) :
    M.det = (-1) ^ (i₀ + j₀ : ℕ) *
      (∑ j, M i₀ j) * (M.submatrix (Fin.succAbove i₀) (Fin.succAbove j₀)).det := by
  rw [← det_transpose, det_eq_sum_column_mul_submatrix_succAbove_succAbove_det _ j₀ i₀
    (by simpa using hv), ← det_transpose, transpose_submatrix, transpose_transpose, add_comm]
  simp_rw [transpose_apply]

end Matrix
