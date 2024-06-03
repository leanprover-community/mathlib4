import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Algebra.Ring.NegOnePow

@[simp]
theorem Int.negOnePow_abs (n : ℤ) : |(n.negOnePow : ℤ)| = 1 := by
  obtain h | h := Int.even_or_odd n
  · rw [negOnePow_even _ h, Units.val_one, abs_one]
  · rw [negOnePow_odd _ h, Units.val_neg, Units.val_one, abs_neg, abs_one]

noncomputable section

open BigOperators Classical Submodule

/-- If we repeat a row of a matrix, we get a matrix of determinant zero. -/
theorem Matrix.det_updateRow_eq_zero {n : Type*} [DecidableEq n] [Fintype n] {R : Type*}
    [CommRing R] (A : Matrix n n R) {k j : n} (h : k ≠ j) :
    (A.updateRow j (A k)).det = 0 := det_zero_of_row_eq h (by simp [h])

/-- If we repeat a column of a matrix, we get a matrix of determinant zero. -/
theorem Matrix.det_updateColumn_eq_zero {n : Type*} [DecidableEq n] [Fintype n] {R : Type*}
    [CommRing R] (A : Matrix n n R) {k j : n} (h : k ≠ j) :
    (A.updateColumn j (fun i ↦ A i k)).det = 0 := by
  rw [← det_transpose, ← updateRow_transpose]
  convert det_updateRow_eq_zero A.transpose h using 1

theorem Matrix.det_updateRow_sum_aux {n : Type*} [DecidableEq n] [Fintype n] {R : Type*}
    [CommRing R] (A : Matrix n n R) {k : n} (s : Finset n) (hk : k ∉ s) (c : n → R) (a : R) :
    (A.updateRow k (a • A k + ∑ j ∈ s, (c j) • A j)).det = a • A.det := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, add_zero, smul_eq_mul, det_updateRow_smul, updateRow_eq_self]
  | @insert j _ hj h_ind =>
      have h : j ≠ k := fun h ↦ (h ▸ hk) (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hj, add_comm ((c j) • A j), ← add_assoc, det_updateRow_add,
        det_updateRow_smul, det_updateRow_eq_zero _ h, mul_zero, add_zero, h_ind]
      exact fun h ↦ hk (Finset.mem_insert_of_mem h)

/-- If we replace a row of a matrix by a linear combination of its rows, then the determinant is
multiplied by the coefficient of this row. -/
theorem Matrix.det_updateRow_sum {n : Type*} [DecidableEq n] [Fintype n] {R : Type*}
    [CommRing R] (A : Matrix n n R) (k : n) (c : n → R) :
    (A.updateRow k (∑ j, (c j) • A j)).det = (c k) • A.det := by
  convert Matrix.det_updateRow_sum_aux A (Finset.univ.erase k) (Finset.univ.not_mem_erase k) c (c k)
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ k)]

/-- If we replace a column of a matrix by a linear combination of its columns, then the determinant
is multiplied by the coefficient of this column. -/
theorem Matrix.det_updateColumn_sum {n : Type*} [DecidableEq n] [Fintype n] {R : Type*}
    [CommRing R] (A : Matrix n n R) (k : n) (c : n → R) :
    (A.updateColumn k (fun k ↦ ∑ j, (c j) • A k j)).det = (c k) • A.det := by
  rw [← det_transpose, ← updateRow_transpose, ← det_transpose A]
  convert Matrix.det_updateRow_sum A.transpose k c
  simp only [smul_eq_mul, Finset.sum_apply, Pi.smul_apply, transpose_apply]

section Fin

namespace Matrix

theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det {R : Type*} [CommRing R]
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin n) R) (hv : ∑ j, M j = 0) (j₁ j₂ : Fin (n + 1)) :
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
        ← neg_eq_iff_eq_neg, ← neg_one_smul R, ← det_updateRow_sum (M.submatrix i.succ.succAbove id)
        i (fun _ ↦ -1), ← Fin.coe_castSucc i, ← h_ind]
      congr
      ext a b
      simp_rw [neg_one_smul, updateRow_apply, Finset.sum_neg_distrib, Pi.neg_apply,
        Finset.sum_apply, submatrix_apply, id_eq]
      split_ifs with h
      · replace hv := congr_fun hv b
        rw [Fin.sum_univ_succAbove _ i.succ, Pi.add_apply, Finset.sum_apply] at hv
        rwa [h, Fin.succAbove_castSucc_self, neg_eq_iff_add_eq_zero, add_comm]
      · obtain h| h := ne_iff_lt_or_gt.mp h
        · rw [Fin.succAbove_castSucc_of_lt _ _ h,  Fin.succAbove_of_succ_le _ _
            (Fin.succ_lt_succ_iff.mpr h).le]
        · rw [Fin.succAbove_succ_of_lt _ _ h, Fin.succAbove_castSucc_of_le _ _ h.le]

theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det' {R : Type*} [CommRing R]
    {n : ℕ} (M : Matrix (Fin n) (Fin (n + 1)) R) (hv : ∀ i, ∑ j, M i j = 0) (j₁ j₂ : Fin (n + 1)) :
    (M.submatrix id (Fin.succAbove j₁)).det =
      Int.negOnePow (j₁ - j₂) • (M.submatrix id (Fin.succAbove j₂)).det := by
  rw [← det_transpose, transpose_submatrix,
    submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det M.transpose ?_ j₁ j₂,
    ← det_transpose, transpose_submatrix, transpose_transpose]
  ext
  simp_rw [Finset.sum_apply, transpose_apply, hv, Pi.zero_apply]
