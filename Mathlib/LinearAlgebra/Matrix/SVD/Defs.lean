/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SVD.Reindex

/-! # Singular Value Decomposition

This file provides the SVD theorem which decomposes a real/complex matrix into left
eigenvectors, singular values block diagonal matrix and right eigenvectors.

Any matrix A (M × N) with rank r = A.rank and with elements in the field ℝ or ℂ can be decomposed
into the product of three matrices `A = UξVᴴ` where:

  * U: an `M × M` matrix containing the left eigenvectors of the matrix
  * ξ: an `M × N` matrix with an `r × r` block in the upper left corner with nonzero singular values
  * V: an `N × N` matrix containing the right eigenvectors of the matrix

Note that:
  * `ξ` is a block matrix `S = [ξ₁₁, ξ₁₂; ξ₂₁, ξ₂₂]` with
    - `ξ₁₁`: a diagonal `r × r` matrix and
    - `ξ₁₂`: r × (N - r) zero matrix, `ξ₂₁` : `(M - r) × r` zero matrix and
    - `ξ₂₂`: (M - r) × (N - r) zero matrix
  * `U` is a block column matrix `U = [U₁ U₂]` with
    - `U₁` : a `M × r` containing left eigenvectors with nonzero singular values.
    - `U₂` : a `M × (M - r)` containing left eigenvectors with zero singular values.
  * `V` is a block column matrix `V = [V₁ V₂]` with
    - `V₁` : a `N × r` containing right eigenvectors with nonzero singular values.
    - `V₂` : a `M` × `(M - r)` containing right eigenvectors with zero singular values.

In many linear algebra materials the matrix of singular values `ξ` is called `Σ`. In Lean4/Mathlib4
this is "reserved" operator. We opted for `ξ` rather than `S` due to its visual similarity to `Σ`.

Since in mathlib the eigenvalues of hermitian matrices are defined in an "arbitrary" undetermined
order, we begin by partitioning the singular values into zero and non-zero values. We partition the
corresponding eigenvectors from AᴴA and AAᴴ using similar rearrangements. These are included in
`Mathlib.LinearAlgebra.Matrix.SVD.Reindex`. The basic API for Column and Row partitioned matrices is
 from `ColumnRowPartitioned`.

Recall that `AᴴA` and `AAᴴ` are Hermitian matrices `docs#Matrix.isHermitian_transpose_mul_self` and
`docs#Matrix.isHermitian_mul_conjTranspose_self`. Hence, they are diagonalizable/decomposable as
`AᴴA = V E Vᴴ` with `E` a matrix of eigenvalues of `AᴴA`. We can apply the reordering/partitioning
from the last paragraph `eigenColumnEquiv` to the columns of `V`, rows and columns of `E` and rows
of `Vᴴ`with out changing the value of the product `VEVᴴ`. With this in mind we have:
    $$AᴴA = V × E × Vᴴ = [V₁ V₂] [μ 0; 0 0] [V₁ᴴ; V₂ᴴ] = V₁μV₁ᴴ$$
where the matrix `μ` is a diagonal matrix containing the non-zero eigenvalues of the matrix AᴴA
ordered so as to correspond to the eigenvectors of AᴴA. This is given the name
`V₁_mul_μ_mul_V₁_conjTranspose` **reduced spectral theorem, right eigenvectors** below.

We can repeat a similar procedure with `AAᴴ = UEUᴴ` and obtain:
    $$AAᴴ = U × E × Uᴴ = [U₁ U₂] [μ' 0; 0 0] [U₁ᴴ; U₂ᴴ] = U₁μ'U₁ᴴ$$
where the matrix `μ'` is a diagonal matrix containing the non-zero eigenvalues of the matrix AAᴴ
ordered so as to correspond to the eigenvectors of AAᴴ. This is given the name
`U₁'_mul_μ'_mul_U₁'_conjTranspose` **reduced spectral theroem, left eigenvectors**

Note that `μ` and `μ'` contain the same values in different orders.

Note that we chose (arbitrarily) to favor the right-eigenvector order. Hence, the matrix `svdσ` is
also the diagonal matrix whose entries are the square roots of the diagonals of `svdμ`. That is
we define `svdξ = [svdσ, 0; 0 0]` with appropriate dimensions for the zero matrices. Further the
following equation holds: `svdξᵀ * svdξ = [μ, 0; 0 0]`

Lemmas `reduced_spectral_theorem` (`reduced_spectral_theorem'`) shows that AᴴA and AAᴴ can be
reduced to products containing only the non-zero singular eigenvalue/eigenvectors. This is later
used in proving the main SVD theorem. A few lemmas are provided about the invertibility of the
non-zero singular values matrix: `svdσ_inv`, `σ_inv_μ_σ_inv_eq_one`, `IsUnit_det_svdσ`,
`IsUnit_det_svdσ_mapK` and `svdσ_inv_mapK`.

We also transfer some of the lemmas we need about eigenvector matrices (for example that
they are unitary: i.e. inverse is conjugate transpose.). Note that since invertibility in mathlib is
defined for square matrices while our matrices are partitioned i.e. N × (N₁ ⊕ N₂) and N ≃ (N ⊕ N₂)
Lean cannot apply the Invertible definition. We work around this where necessary.

To make relating left eigenvectors to right eigenvectors easier we define U₁ = AV₁σ⁻¹ while U₂ is
obtained from the eigenvectors of (AAᴴ). This avoid a lengthy reindexing operation with many proofs.
The vectors in U₂ have no such issue since they are multiplied by zero singular values anyway.

## Tags
Singular Value decomposition, SVD
-/

variable {𝕂 : Type*} [IsROrC 𝕂] [DecidableEq 𝕂]
variable {M N : ℕ}

open Matrix BigOperators

namespace Matrix

/-- The right eigenvectors of a matrix A corresponding to its non-zero eigenvalues -/
noncomputable def svdV₁ (A : Matrix (Fin M) (Fin N) 𝕂) : Matrix (Fin N) (Fin (A.rank)) 𝕂 :=
  ((reindex (Equiv.refl (Fin N)) (eigenColumnEquiv A))
    (isHermitian_transpose_mul_self A).eigenvectorMatrix).toColumns₁

/-- The right eigenvectors of a matrix A corresponding to the zero eigenvalues of the matrix AᴴA -/
noncomputable def svdV₂ (A : Matrix (Fin M) (Fin N) 𝕂) : Matrix (Fin N) (Fin (N - A.rank)) 𝕂 :=
  ((reindex (Equiv.refl (Fin N)) (eigenColumnEquiv A))
    (isHermitian_transpose_mul_self A).eigenvectorMatrix).toColumns₂

/-- The diagonal matrix containing the non-zero eigenvalues of matrix Aᴴ * A These are also the
squares of the non-zero singular values of the matrix A. Note that these are the same elements as in
`svdμ'` but permuted in some arbitrary order -/
noncomputable def svdμ (A : Matrix (Fin M) (Fin N) 𝕂) : Matrix (Fin A.rank) (Fin A.rank) ℝ :=
  (reindex
    (finRankEquivEigsConjTransposeMulSelf A).symm
    (finRankEquivEigsConjTransposeMulSelf A).symm)
  (diagonal (fun (i : {a // (isHermitian_transpose_mul_self A).eigenvalues a ≠ 0}) =>
      (isHermitian_transpose_mul_self A).eigenvalues i))

/-- The diagonal matrix containing the non-zero eigenvalues of matrix A * Aᴴ These are also the
squares of the non-zero singular values of the matrix A. Note that these are the same elements as in
`svdμ` but permuted in some arbitrary order -/
noncomputable def svdμ' (A : Matrix (Fin M) (Fin N) 𝕂) : Matrix (Fin A.rank) (Fin A.rank) ℝ :=
  (reindex
    (finRankEquivEigsMulConjTranspose A).symm
    (finRankEquivEigsMulConjTranspose A).symm)
  (diagonal (fun (i : {a // (isHermitian_mul_conjTranspose_self A).eigenvalues a ≠ 0}) =>
      (isHermitian_mul_conjTranspose_self A).eigenvalues i))

/-- The diagonal matrix containing the non-zero singular values of matrix A. These are also the
square roots of the non-zero eigenvalues of the matrix Aᴴ * A. -/
noncomputable def svdσ (A : Matrix (Fin M) (Fin N) 𝕂) : Matrix (Fin A.rank) (Fin A.rank) ℝ :=
  (reindex
    (finRankEquivEigsConjTransposeMulSelf A).symm
    (finRankEquivEigsConjTransposeMulSelf A).symm)
  (diagonal (fun (i : {a // (isHermitian_transpose_mul_self A).eigenvalues a ≠ 0}) =>
      Real.sqrt ((isHermitian_transpose_mul_self A).eigenvalues i)))

/-- The left eigenvectors of a matrix A corresponding to its non-zero eigenvalues, obtained as the
image of the corresponding right eigenvectors. The transformation is given by the matrix itself and
scaling by the singular values. -/
noncomputable def svdU₁ (A : Matrix (Fin M) (Fin N) 𝕂) : Matrix (Fin M) (Fin A.rank) 𝕂 :=
  A * A.svdV₁ * (A.svdσ.map (algebraMap ℝ 𝕂))⁻¹

/-- The left eigenvectors of a matrix A corresponding to its non-zero eigenvalues, obtained directly
from the eigendecomposition of the AAᴴ matrix. These do NOT share the same ordering as `svdU₁`. -/
noncomputable def svdU₁' (A : Matrix (Fin M) (Fin N) 𝕂) : Matrix (Fin M) (Fin (A.rank)) 𝕂 :=
  ((reindex (Equiv.refl (Fin M)) (eigenRowEquiv A))
    (isHermitian_mul_conjTranspose_self A).eigenvectorMatrix).toColumns₁

/-- The left eigenvectors of a matrix A corresponding to its zero eigenvalues, obtained directly
from the eigendecomposition of the AAᴴ matrix. The order of these eigenvectors is not relevant as
they are multiplied by zero anyway. Hence we do not have `svdU₂` -/
noncomputable def svdU₂ (A : Matrix (Fin M) (Fin N) 𝕂) : Matrix (Fin M) (Fin (M - A.rank)) 𝕂 :=
  ((reindex (Equiv.refl (Fin M)) (eigenRowEquiv A))
    (isHermitian_mul_conjTranspose_self A).eigenvectorMatrix).toColumns₂

/-- Concatenation of the left eigenvectors U₁ and U₂ into one eigenvector matrix. This is a unitary
matrix. Note however we cannot use `Matrix.unitaryGroup` because the indices of the rows and columns
do not match. -/
noncomputable def svdU (A : Matrix (Fin M) (Fin N) 𝕂) :
    Matrix (Fin M) (Fin (A.rank) ⊕ Fin (M - A.rank)) 𝕂 := fromColumns A.svdU₁ A.svdU₂

/-- Concatenation of the right eigenvectors V₁ and V₂ into one eigenvector matrix. This is a unitary
matrix. Note however we cannot use `Matrix.unitaryGroup` because the indices of the rows and columns
do not match.-/
noncomputable def svdV (A : Matrix (Fin M) (Fin N) 𝕂) :
    Matrix (Fin N) (Fin (A.rank) ⊕ Fin (N - A.rank)) 𝕂 := fromColumns A.svdV₁ A.svdV₂

/-- Given a matrix A of size m × n: `svdξ` is a matrix of the same dimensions but partitioned into
four blocks such that S₁₁ contains the non-zero singular values, ξ₁₂, ξ₂₁ and ξ₂₂ are zeros. The ξ₁₁
block is the diagonal matrix `svdσ` above. -/
noncomputable def svdξ (A : Matrix (Fin M) (Fin N) 𝕂) :
    Matrix (Fin (A.rank) ⊕ Fin (M - A.rank)) (Fin (A.rank) ⊕ Fin (N - A.rank)) 𝕂 :=
  (fromBlocks ((A.svdσ).map (algebraMap ℝ 𝕂)) 0 0 0)

lemma reindex_eigenRowEquiv_eigenvectorMatrix (A : Matrix (Fin M) (Fin N) 𝕂) :
  ((reindex (Equiv.refl (Fin M)) (eigenRowEquiv A))
    (isHermitian_mul_conjTranspose_self A).eigenvectorMatrix) = fromColumns A.svdU₁' A.svdU₂ := by
  rw [svdU₂, svdU₁']
  simp only [reindex_apply, Equiv.refl_symm, Equiv.coe_refl, fromColumns_toColumns]

lemma V₁_conjTranspose_mul_V₁ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdV₁ᴴ * A.svdV₁ = 1 := by
  simp_rw [svdV₁, toColumns₁, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_apply,
    id_eq, HMul.hMul, dotProduct, conjTranspose_apply, of_apply, ← conjTranspose_apply,
    IsHermitian.conjTranspose_eigenvectorMatrix, ← mul_apply,
    Matrix.mul_eq_one_comm.1 (IsHermitian.eigenvectorMatrix_mul_inv _), one_apply,
    EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
  rfl

lemma V₂_conjTranspose_mul_V₂ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdV₂ᴴ * A.svdV₂ = 1 := by
  simp_rw [svdV₂, toColumns₂, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    submatrix_apply, id_eq, HMul.hMul, dotProduct, conjTranspose_apply, of_apply,
    ← conjTranspose_apply, IsHermitian.conjTranspose_eigenvectorMatrix, ← mul_apply,
    Matrix.mul_eq_one_comm.1 (IsHermitian.eigenvectorMatrix_mul_inv _), one_apply,
    EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq]
  rfl

lemma V₂_conjTranspose_mul_V₁ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdV₂ᴴ * A.svdV₁ = 0 := by
  simp_rw [svdV₂, toColumns₂, svdV₁, toColumns₁, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    submatrix_apply, id_eq, HMul.hMul, dotProduct, conjTranspose_apply, of_apply,
    ← conjTranspose_apply, IsHermitian.conjTranspose_eigenvectorMatrix, ← mul_apply,
    Matrix.mul_eq_one_comm.1 (IsHermitian.eigenvectorMatrix_mul_inv _), one_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma V₁_conjTranspose_mul_V₂ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdV₁ᴴ * A.svdV₂ = 0 := by
  simp_rw [svdV₂, toColumns₂, svdV₁, toColumns₁, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    submatrix_apply, id_eq, HMul.hMul, dotProduct, conjTranspose_apply, of_apply,
    ← conjTranspose_apply, IsHermitian.conjTranspose_eigenvectorMatrix, ← mul_apply,
    Matrix.mul_eq_one_comm.1 (IsHermitian.eigenvectorMatrix_mul_inv _), one_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma V_conjTranspose_mul_V (A : Matrix (Fin M) (Fin N) 𝕂) : (A.svdV)ᴴ * (A.svdV) = 1 := by
  rw [svdV, conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromRows_mul_fromColumns,
    V₁_conjTranspose_mul_V₂, V₁_conjTranspose_mul_V₁, V₂_conjTranspose_mul_V₂,
    V₂_conjTranspose_mul_V₁, fromBlocks_one]

lemma V_mul_conjTranspose_V (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdV * A.svdVᴴ = 1 := by
  rw [svdV, conjTranspose_fromColumns_eq_fromRows_conjTranspose,
    fromColumns_mul_fromRows_eq_one_comm, ← conjTranspose_fromColumns_eq_fromRows_conjTranspose,
    ← svdV, V_conjTranspose_mul_V]
  exact eigenColumnEquiv A

@[simp]
lemma ξ_toBlocks₁₁ (A : Matrix (Fin M) (Fin N) 𝕂) :
    A.svdξ.toBlocks₁₁ = A.svdσ.map (algebraMap ℝ 𝕂) := rfl

@[simp]
lemma ξ_toBlocks₁₂ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdξ.toBlocks₁₂ = 0 := rfl

@[simp]
lemma ξ_toBlocks₂₁ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdξ.toBlocks₂₁ = 0 := rfl

@[simp]
lemma ξ_toBlocks₂₂ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdξ.toBlocks₂₂ = 0 := rfl

lemma conjTranspose_svdσ_eq_svdσ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdσᴴ = A.svdσ := by
  rw [conjTranspose_eq_transpose_of_trivial, svdσ]
  simp

lemma μ_block (A : Matrix (Fin M) (Fin N) 𝕂) :
    (reindex (eigenColumnEquiv A) (eigenColumnEquiv A))
      (diagonal ( (isHermitian_transpose_mul_self A).eigenvalues)) =
        fromBlocks A.svdμ 0 0 0 := by
  rw [reindex_apply, submatrix_diagonal_equiv, svdμ]
  funext i j
  cases' j with j j <;> cases' i with i i <;>
  simp [diagonal_apply]
  rfl

lemma μ'_block (A : Matrix (Fin M) (Fin N) 𝕂) :
    (reindex (eigenRowEquiv A) (eigenRowEquiv A))
        (diagonal ( (isHermitian_mul_conjTranspose_self A).eigenvalues)) =
          fromBlocks A.svdμ' 0 0 0 := by
  rw [reindex_apply, submatrix_diagonal_equiv, svdμ']
  funext i j
  cases' j with j j <;> cases' i with i i <;>
  simp [diagonal_apply]
  rfl

lemma reindex_eigenColumnEquiv_eigenvectorMatrix (A : Matrix (Fin M) (Fin N) 𝕂) :
    (reindex (Equiv.refl (Fin N)) (eigenColumnEquiv A))
      (isHermitian_transpose_mul_self A).eigenvectorMatrix =
      fromColumns A.svdV₁ A.svdV₂ := by
  rw [reindex_apply, fromColumns, svdV₁, svdV₂, toColumns₁, toColumns₂]
  funext i j
  cases' j with j j <;>
  simp only [Equiv.refl_symm, Equiv.coe_refl, submatrix_apply, id_eq,
    reindex_apply, of_apply, Sum.elim_inl, Sum.elim_inr]

/-- **Reduced spectral theorem**, right eigenvector version. -/
lemma V₁_mul_μ_mul_V₁_conjTranspose (A : Matrix (Fin M) (Fin N) 𝕂) :
    A.svdV₁ * (A.svdμ.map (algebraMap ℝ 𝕂)) * A.svdV₁ᴴ = Aᴴ * A := by
  let hAHA := isHermitian_transpose_mul_self A
  -- "Ugly" (submatrix_mul_equiv) explicit rewrites: each one on its own line for
  -- readability!!
  rw [eq_comm, ← submatrix_id_id (Aᴴ * A), IsHermitian.spectral_theorem' hAHA,
    ← IsHermitian.conjTranspose_eigenvectorMatrix, Matrix.mul_assoc,
    ← submatrix_mul_equiv
      hAHA.eigenvectorMatrix (diagonal (IsROrC.ofReal ∘ hAHA.eigenvalues)  *
      (hAHA.eigenvectorMatrixᴴ)) _ (eigenColumnEquiv A).symm _,
    ← submatrix_mul_equiv (diagonal (IsROrC.ofReal ∘ hAHA.eigenvalues)) (hAHA.eigenvectorMatrixᴴ)
    _ (eigenColumnEquiv A).symm _,
    ← @IsROrC.algebraMap_eq_ofReal 𝕂]
  simp_rw [Function.comp]
  rw [← diagonal_map, submatrix_map, ← reindex_apply, ← Equiv.coe_refl, ← Equiv.refl_symm,
    ← reindex_apply, ←conjTranspose_submatrix, ← reindex_apply, μ_block,
    reindex_eigenColumnEquiv_eigenvectorMatrix,
    conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromBlocks_map, fromBlocks_mul_fromRows,
    fromColumns_mul_fromRows]
  simp only [map_zero, Matrix.map_zero, Matrix.zero_mul, add_zero, Matrix.mul_zero]
  rw [Matrix.mul_assoc]
  apply map_zero

/-- **Reduced spectral theorem**, left eigenvector version. -/
lemma U₁'_mul_μ'_mul_U₁'_conjTranspose (A : Matrix (Fin M) (Fin N) 𝕂) :
    A.svdU₁' * (A.svdμ'.map (algebraMap ℝ 𝕂)) * A.svdU₁'ᴴ = A * Aᴴ := by
  let hAAH := isHermitian_mul_conjTranspose_self A
  rw [eq_comm, ← submatrix_id_id (A * Aᴴ), IsHermitian.spectral_theorem' hAAH,
    ← IsHermitian.conjTranspose_eigenvectorMatrix, Matrix.mul_assoc,
    ← submatrix_mul_equiv hAAH.eigenvectorMatrix
      (diagonal (IsROrC.ofReal ∘ hAAH.eigenvalues) * (hAAH.eigenvectorMatrixᴴ)) _
        (eigenRowEquiv A).symm _,
    ← submatrix_mul_equiv (diagonal (IsROrC.ofReal ∘ hAAH.eigenvalues))
      (hAAH.eigenvectorMatrixᴴ) _ (eigenRowEquiv A).symm _,
      ← @IsROrC.algebraMap_eq_ofReal 𝕂]
  simp_rw [Function.comp]
  rw [← diagonal_map, submatrix_map,
    ← reindex_apply, ← Equiv.coe_refl, ← Equiv.refl_symm, ← reindex_apply,
    ← conjTranspose_submatrix, ← reindex_apply, μ'_block, reindex_eigenRowEquiv_eigenvectorMatrix,
    conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromBlocks_map,
    fromBlocks_mul_fromRows, fromColumns_mul_fromRows]
  simp only [map_zero, Matrix.map_zero, Matrix.zero_mul, add_zero, Matrix.mul_zero]
  rw [Matrix.mul_assoc]
  rw [map_zero]

open scoped ComplexOrder

lemma eigenvalues_conjTranspose_mul_self_nonneg {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n 𝕂} :
    ∀ i , 0 ≤ (isHermitian_transpose_mul_self A).eigenvalues i :=
  Matrix.PosSemidef.eigenvalues_nonneg (Matrix.posSemidef_conjTranspose_mul_self _)

lemma eigenvalues_self_mul_conjTranspose_nonneg {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] {A : Matrix m n 𝕂} :
    ∀ i , 0 ≤ (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  Matrix.PosSemidef.eigenvalues_nonneg (Matrix.posSemidef_self_mul_conjTranspose _)

lemma svdσ_inv (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdσ⁻¹ =
    (reindex
      (finRankEquivEigsConjTransposeMulSelf A).symm
      (finRankEquivEigsConjTransposeMulSelf A).symm)
      (diagonal (fun (i : {a // (isHermitian_transpose_mul_self A).eigenvalues a ≠ 0}) =>
        1 / Real.sqrt ((isHermitian_transpose_mul_self A).eigenvalues i))) := by
  apply inv_eq_right_inv
  rw [svdσ]
  simp only [ne_eq, reindex_apply, submatrix_diagonal_equiv, diagonal_mul_diagonal,
    Function.comp_apply]
  rw [← diagonal_one, diagonal_eq_diagonal_iff]
  intros i
  rw [mul_one_div_cancel]
  exact (Real.sqrt_ne_zero (eigenvalues_conjTranspose_mul_self_nonneg _)).2
    ((finRankEquivEigsConjTransposeMulSelf A).1 i).prop

lemma σ_inv_μ_σ_inv_eq_one (A : Matrix (Fin M) (Fin N) 𝕂) :
    (A.svdσ⁻¹) * A.svdμ * A.svdσ⁻¹ = 1 := by
  rw [svdσ_inv, svdμ]
  simp only [ne_eq, one_div, reindex_apply, submatrix_diagonal_equiv, diagonal_conjTranspose,
    star_trivial, diagonal_mul_diagonal, Function.comp_apply]
  rw [← diagonal_one, diagonal_eq_diagonal_iff]
  intro i
  rw [mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt, inv_mul_cancel]
  exact ((finRankEquivEigsConjTransposeMulSelf A).1 i).prop
  exact (eigenvalues_conjTranspose_mul_self_nonneg _)

lemma IsUnit_det_svdσ (A : Matrix (Fin M) (Fin N) 𝕂) : IsUnit (A.svdσ.det) := by
  unfold svdσ
  rw [reindex_apply]
  simp only [ne_eq, submatrix_diagonal_equiv, det_diagonal, Function.comp_apply]
  apply Ne.isUnit _
  exact Finset.prod_ne_zero_iff.2 ( fun i _ =>
    (Real.sqrt_ne_zero (eigenvalues_conjTranspose_mul_self_nonneg _)).2
      ((finRankEquivEigsConjTransposeMulSelf A).1 i).prop)

lemma IsUnit_det_svdσ_mapK (A : Matrix (Fin M) (Fin N) 𝕂) :
    IsUnit (det (map A.svdσ (algebraMap ℝ 𝕂))) := by
  unfold svdσ
  simp only [ne_eq, reindex_apply, submatrix_diagonal_equiv, map_zero, diagonal_map,
    Function.comp_apply, det_diagonal]
  rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i
  simp only [Finset.mem_univ, ne_eq, map_eq_zero, forall_true_left]
  apply (Real.sqrt_ne_zero (eigenvalues_conjTranspose_mul_self_nonneg _)).2
      ((finRankEquivEigsConjTransposeMulSelf A).1 i).prop

lemma svdσ_inv_mapK (A : Matrix (Fin M) (Fin N) 𝕂) :
    (map (A.svdσ) (algebraMap ℝ 𝕂))⁻¹ = (map (A.svdσ)⁻¹ (algebraMap ℝ 𝕂)) := by
  apply inv_eq_left_inv
  rw [← map_mul, nonsing_inv_mul]
  simp only [map_zero, _root_.map_one, map_one]
  apply IsUnit_det_svdσ

lemma mul_V₂_eq_zero (A : Matrix (Fin M) (Fin N) 𝕂) :
    A * A.svdV₂ = 0 := by
  suffices h : Aᴴ * A * A.svdV₂ = 0
  · exact (conjTranspose_mul_self_mul_eq_zero _ _).1 h
  rw [←V₁_mul_μ_mul_V₁_conjTranspose, Matrix.mul_assoc, V₁_conjTranspose_mul_V₂, Matrix.mul_zero]

lemma U₁_mul_μ_mul_U₁_conjTranspose (A : Matrix (Fin M) (Fin N) 𝕂) :
    A.svdU₁ * (A.svdμ.map (algebraMap ℝ 𝕂)) * A.svdU₁ᴴ = A * Aᴴ := by
  unfold svdU₁
  have h1 : A * A.svdV₂ * (A * A.svdV₂)ᴴ = 0 := by rw [mul_V₂_eq_zero, Matrix.zero_mul]
  have h2 : A.svdV * A.svdVᴴ = A.svdV₁ * A.svdV₁ᴴ + A.svdV₂ * A.svdV₂ᴴ := by
    rw [svdV, conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromColumns_mul_fromRows]

  rw [svdσ_inv_mapK, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc (A * A.svdV₁) , ← Matrix.map_mul, Matrix.mul_assoc (A * A.svdV₁),
    ← Matrix.conjTranspose_map, ← Matrix.mul_assoc _ _ (A.svdV₁ᴴ * Aᴴ), ← Matrix.map_mul,
    conjTranspose_nonsing_inv, conjTranspose_svdσ_eq_svdσ, σ_inv_μ_σ_inv_eq_one,
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.one_mul, ← conjTranspose_mul,
    ← add_zero ((A*A.svdV₁) * ( A*A.svdV₁)ᴴ), ← h1, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_add, conjTranspose_mul, conjTranspose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.add_mul, ← h2, V_mul_conjTranspose_V, Matrix.one_mul]
  intros x
  rw [IsROrC.star_def, IsROrC.algebraMap_eq_ofReal, starRingEnd_apply, star_trivial,
    IsROrC.star_def, IsROrC.conj_ofReal]

lemma U₁_conjTranspose_mul_U₁ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdU₁ᴴ * A.svdU₁ = 1 := by
  rw [svdU₁, conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ←V₁_mul_μ_mul_V₁_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ A.svdV₁, V₁_conjTranspose_mul_V₁, Matrix.one_mul,
    Matrix.mul_assoc A.svdV₁, ← Matrix.mul_assoc _ A.svdV₁, V₁_conjTranspose_mul_V₁,
    Matrix.one_mul, svdσ_inv_mapK, ← conjTranspose_map, ← Matrix.map_mul, ← Matrix.map_mul,
    ← Matrix.mul_assoc, conjTranspose_nonsing_inv, conjTranspose_svdσ_eq_svdσ, σ_inv_μ_σ_inv_eq_one]
  simp only [map_zero, _root_.map_one, map_one]
  intros x
  rw [IsROrC.star_def, IsROrC.algebraMap_eq_ofReal, starRingEnd_apply, star_trivial,
    IsROrC.star_def, IsROrC.conj_ofReal]

lemma U₂_conjTranspose_mul_U₂ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdU₂ᴴ * A.svdU₂ = 1 := by
  rw [svdU₂, toColumns₂]
  simp only [reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_apply, id_eq]
  funext i j
  simp_rw [Matrix.mul_apply, conjTranspose_apply, of_apply,
    ← conjTranspose_apply, IsHermitian.conjTranspose_eigenvectorMatrix,
    ← Matrix.mul_apply, Matrix.mul_eq_one_comm.1 (IsHermitian.eigenvectorMatrix_mul_inv _)]
  by_cases hij: i = j
  · simp_rw [hij, one_apply_eq]
  · rw [one_apply_ne hij, one_apply_ne]
    simpa only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq]

lemma U₁'_conjTranspose_mul_U₂ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdU₁'ᴴ * A.svdU₂ = 0 := by
  simp_rw [svdU₁', svdU₂, toColumns₁, toColumns₂, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    submatrix_apply, id_eq, HMul.hMul, dotProduct, conjTranspose_apply, of_apply,
    ← conjTranspose_apply, IsHermitian.conjTranspose_eigenvectorMatrix, ← mul_apply,
    Matrix.mul_eq_one_comm.1 (IsHermitian.eigenvectorMatrix_mul_inv _)]
  funext i j
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true, one_apply_ne, zero_apply]

lemma conjTranspose_mul_U₂_eq_zero (A : Matrix (Fin M) (Fin N) 𝕂) : Aᴴ * A.svdU₂ = 0 := by
  suffices h : A * Aᴴ * A.svdU₂ = 0
  · exact (self_mul_conjTranspose_mul_eq_zero _ _).1 h
  rw [←U₁'_mul_μ'_mul_U₁'_conjTranspose, Matrix.mul_assoc, U₁'_conjTranspose_mul_U₂]
  simp only [Matrix.mul_zero]

lemma U₁_conjTranspose_mul_U₂ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdU₁ᴴ * A.svdU₂ = 0 := by
  unfold svdU₁
  simp_rw [conjTranspose_mul, Matrix.mul_assoc, conjTranspose_mul_U₂_eq_zero, Matrix.mul_zero]

lemma U₂_conjTranspose_mul_U₁ (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdU₂ᴴ * A.svdU₁ = 0 := by
  rw [← conjTranspose_conjTranspose (A.svdU₁), ← conjTranspose_mul, U₁_conjTranspose_mul_U₂,
    conjTranspose_zero]

lemma U_conjTranspose_mul_U (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdUᴴ * A.svdU = 1 := by
  rw [svdU, conjTranspose_fromColumns_eq_fromRows_conjTranspose, fromRows_mul_fromColumns,
    U₁_conjTranspose_mul_U₂, U₁_conjTranspose_mul_U₁, U₂_conjTranspose_mul_U₂,
    U₂_conjTranspose_mul_U₁, fromBlocks_one]

lemma U_mul_U_conjTranspose (A : Matrix (Fin M) (Fin N) 𝕂) : A.svdU * A.svdUᴴ = 1 := by
  rw [svdU, conjTranspose_fromColumns_eq_fromRows_conjTranspose,
    fromColumns_mul_fromRows_eq_one_comm, ← conjTranspose_fromColumns_eq_fromRows_conjTranspose,
    ←svdU, U_conjTranspose_mul_U ]
  exact eigenRowEquiv A

/-- **Singular Value Decomposition (SVD) Theorem**
Any matrix A (M × N) with rank r = A.rank and  with elements in ℝ or ℂ fields can be decompsed
into three matrices:
  * U: an M × M matrix containing the left eigenvectors of the matrix
  * S: an M × N matrix with an r × r block in the upper left corner with nonzero singular values
  * V: an N × N matrix containing the right eigenvectors of the matrix

Note that UUᴴ = UᴴU = 1 and VVᴴ=VᴴV = 1 as proven in `V_conjTranspose_mul_V`,`V_mul_conjTranspose_V`
`U_conjTranspose_mul_U` and  `U_mul_U_conjTranspose`-/

theorem U_mul_S_mul_V_conjTranspose (A : Matrix (Fin M) (Fin N) 𝕂) :
    A.svdU * A.svdξ * A.svdVᴴ = A := by
  apply_fun (fun x => x * A.svdV)
  simp_rw [svdU, Matrix.mul_assoc, V_conjTranspose_mul_V, Matrix.mul_one, svdξ,
    fromColumns_mul_fromBlocks, svdV, mul_fromColumns, Matrix.mul_zero, add_zero,
    fromColumns_ext_iff, mul_V₂_eq_zero, and_true, svdU₁,
    Matrix.nonsing_inv_mul_cancel_right _ _ (IsUnit_det_svdσ_mapK _)]
  exact Matrix.mul_left_injective_of_inv _ _ (V_mul_conjTranspose_V _)

end Matrix
