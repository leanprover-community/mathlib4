/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.SVD.IsROrCStarOrderedRing
import Mathlib.LinearAlgebra.Matrix.SVD.RankMulIsUnit
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Hermitian matrices rank

This file proves that the rank of a Hermitian matrix is the same as the count of non-zero
eigenvaules. To achieve this result we re-express the spectral theorem, as A = V D Vᴴ instead of
VᴴA = V D as in the current version of `spectral_theroem` in `mathlib`. For convenience, we state
the left inverse version of `eigenvectorMatrix_mul_inv`. Then we express the rank of the diagonal
matrix in terms of count of non-zero diagonal entries `rank_diagonal_matrix`(instead of linear maps)

We then use the fact that AAᴴ and AᴴA have the same rank as A to show
`rank_eq_card_pos_eigs_conj_transpose_mul_self` and `rank_eq_card_pos_eigs_self_mul_conj_transpose`
to show that the count non-zero eigenvalues are the same as rank of A.
 -/

open Matrix BigOperators

namespace Matrix
lemma modified_spectral_theorem {n R: Type}
  [Fintype n][DecidableEq n][IsROrC R][DecidableEq R]
  {A: Matrix n n R}(hA: A.IsHermitian) :
  A = (hA.eigenvectorMatrix) ⬝
    ((Matrix.diagonal (IsROrC.ofReal ∘ hA.eigenvalues)) ⬝ hA.eigenvectorMatrixInv) := by
  have h := hA.spectral_theorem
  replace h := congr_arg (λ x => hA.eigenvectorMatrix ⬝  x) h
  dsimp only at h
  rwa [← Matrix.mul_assoc, hA.eigenvectorMatrix_mul_inv, Matrix.one_mul] at h

lemma eigenvector_matrix_inv_mul_self {n R: Type}
  [Fintype n][DecidableEq n][IsROrC R][DecidableEq R]
  {A: Matrix n n R}(hA: A.IsHermitian) :
  (hA.eigenvectorMatrixInv)⬝(hA.eigenvectorMatrix) = 1 :=
  (mul_eq_one_comm.1 hA.eigenvectorMatrix_mul_inv)

lemma rank_diagonal_matrix{n R: Type}
  [Fintype n][DecidableEq n] [Field R][DecidableEq R]
  (w: n → R) :
  ((Matrix.diagonal w).rank) = ↑(Fintype.card {i // (w i) ≠ 0}) := by
  have hu : Set.univ ⊆ {i : n | w i = 0}ᶜ ∪ {i : n | w i = 0} := by
    rw [Set.compl_union_self]
  have hd : Disjoint {i : n | w i ≠ 0} {i : n | w i = 0} := disjoint_compl_left
  have B₁ := LinearMap.iSup_range_stdBasis_eq_iInf_ker_proj R (λ _:n => R) hd hu (Set.toFinite _)
  have B₂ := LinearMap.iInfKerProjEquiv R (fun _ ↦ R) hd hu
  rw [Matrix.rank, ← Matrix.toLin'_apply', range_diagonal, B₁,
    ← FiniteDimensional.finrank_fintype_fun_eq_card R]
  apply LinearEquiv.finrank_eq
  apply B₂


lemma rank_eq_rank_diagonal {n R: Type}[Fintype n][DecidableEq n]
  [IsROrC R][DecidableEq R]
  {A: Matrix n n R}(hA: A.IsHermitian) :
  A.rank = (Matrix.diagonal (hA.eigenvalues)).rank := by
  nth_rewrite 1 [modified_spectral_theorem hA]

  have hE := Matrix.isUnit_det_of_invertible (hA.eigenvectorMatrix)
  have hiE := Matrix.isUnit_det_of_invertible (hA.eigenvectorMatrixInv)
  rw [rank_IsUnit_mul hA.eigenvectorMatrix _ hE]
  rw [rank_mul_IsUnit hA.eigenvectorMatrixInv _ hiE]
  rw [rank_diagonal_matrix, rank_diagonal_matrix]
  simp only [Function.comp_apply, ne_eq, algebraMap.lift_map_eq_zero_iff,
    Fintype.card_subtype_compl, ge_iff_le]

lemma rank_eq_count_non_zero_eigs {n R: Type}[Fintype n][DecidableEq n]
  [IsROrC R][DecidableEq R]
  (A: Matrix n n R)(hA: A.IsHermitian) :
  A.rank =  (Fintype.card {i // hA.eigenvalues i ≠ 0}) := by
  rw [rank_eq_rank_diagonal hA, rank_diagonal_matrix]

lemma rank_eq_card_pos_eigs_conj_transpose_mul_self {m n R: Type}
  [Fintype m][Fintype n][DecidableEq m][DecidableEq n][IsROrC R][DecidableEq R]
  (A: Matrix m n R):
  A.rank =  (Fintype.card {i // (Matrix.isHermitian_transpose_mul_self A).eigenvalues i ≠ 0}) := by
  rw [← rank_conjTranspose_mul_self]
  rw [← rank_eq_count_non_zero_eigs ]

lemma rank_eq_card_pos_eigs_self_mul_conj_transpose {m n R: Type}
  [Fintype m][Fintype n][DecidableEq m][DecidableEq n][IsROrC R][DecidableEq R]
  (A: Matrix m n R): A.rank =
  (Fintype.card {i // (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0}) := by
  rw [← rank_self_mul_conjTranspose]
  rw [← rank_eq_count_non_zero_eigs]

end Matrix
