/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Hermitian

#align_import linear_algebra.matrix.spectrum from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-! # Spectral theory of hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem

-/


namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
variable {A : Matrix n n 𝕜}

open scoped BigOperators

namespace IsHermitian

section DecidableEq

variable [DecidableEq n]
variable (hA : A.IsHermitian)

/-- The eigenvalues of a hermitian matrix, indexed by `Fin (Fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : Fin (Fintype.card n) → ℝ :=
  (isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace
#align matrix.is_hermitian.eigenvalues₀ Matrix.IsHermitian.eigenvalues₀

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ := fun i =>
  hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
#align matrix.is_hermitian.eigenvalues Matrix.IsHermitian.eigenvalues

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  ((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))
#align matrix.is_hermitian.eigenvector_basis Matrix.IsHermitian.eigenvectorBasis

variable (m: Type*) [Fintype m]
@[simp]
theorem toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin M v =
    (WithLp.equiv 2 (m → 𝕜)).symm (M *ᵥ (WithLp.equiv 2 (n → 𝕜)) v) := rfl

lemma mulVec_eigenvectorBasis (j : n) :
   A *ᵥ ⇑(hA.eigenvectorBasis j) =
        (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j)  := by
  simpa only [eigenvectorBasis, OrthonormalBasis.reindex_apply, toEuclideanLin_apply,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
    congr(⇑$((isHermitian_iff_isSymmetric.1 hA).apply_eigenvectorBasis
     finrank_euclideanSpace ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)))

/--Unitary matrix whose columns are Orthonormal Basis of Eigenvectors of Hermitian Matrix-/
noncomputable def eigenvectorUnitary {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n]{A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    Matrix.unitaryGroup n 𝕜 :=
    ⟨(EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
    (EuclideanSpace.basisFun n 𝕜) (eigenvectorBasis hA)⟩

/--The coercion from the subtype eigenvectorUnitary to the underlying matrix-/
lemma eigenvectorUnitary_coe {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    eigenvectorUnitary hA =
      (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis :=
  rfl

@[simp]
theorem eigenvectorUnitary_apply (i j : n) :
    eigenvectorUnitary hA i j = ⇑(hA.eigenvectorBasis j) i :=
  rfl

theorem eigenvectorUnitary_mulVec (j : n) :
eigenvectorUnitary hA *ᵥ Pi.single j 1 = ⇑(hA.eigenvectorBasis j)
:=by simp only [mulVec_single, eigenvectorUnitary_apply, mul_one]

theorem star_eigenvectorUnitary_mulVec (j : n) :
(star (eigenvectorUnitary hA : Matrix n n 𝕜)) *ᵥ ⇑(hA.eigenvectorBasis j) =
Pi.single j 1 := by
rw [←eigenvectorUnitary_mulVec, mulVec_mulVec, unitary.coe_star_mul_self, one_mulVec]

/-- **Diagonalization theorem**, **spectral theorem** for matrices; A hermitian matrix can be
diagonalized by a change of basis.

For the spectral theorem on linear maps, see
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`. -/
theorem spectral_theorem1 :
    (star (eigenvectorUnitary hA : Matrix n n 𝕜)) * A * (eigenvectorUnitary hA : Matrix n n 𝕜)
     = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
apply Matrix.toEuclideanLin.injective
apply Basis.ext (EuclideanSpace.basisFun n 𝕜).toBasis
intro i
rw [toEuclideanLin_apply, toEuclideanLin_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, WithLp.equiv_single, ←mulVec_mulVec,
    eigenvectorUnitary_mulVec, ←mulVec_mulVec, mulVec_eigenvectorBasis,
    Matrix.diagonal_mulVec_single, mulVec_smul, star_eigenvectorUnitary_mulVec,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.equiv_symm_smul, WithLp.equiv_symm_single,
    Function.comp_apply, mul_one, WithLp.equiv_symm_single]
apply PiLp.ext
intro j
simp only [PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- *spectral theorem* (Alternate form for convenience) A hermitian matrix can be can be
replaced by a diagonal matrix sandwiched between the eigenvector unitaries. This alternate form
allows direct rewriting of A since: <| A = V D V⁻¹$ -/
theorem spectral_theorem2 :
        A = (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ hA.eigenvalues)
        * (star (eigenvectorUnitary hA : Matrix n n 𝕜)) := by
rw [←spectral_theorem1, mul_assoc, mul_assoc,
   (Matrix.mem_unitaryGroup_iff).mp (eigenvectorUnitary hA).2, mul_one,
   ←mul_assoc, (Matrix.mem_unitaryGroup_iff).mp (eigenvectorUnitary hA).2, one_mul]

theorem spectral_theorem3 :
      (star (eigenvectorUnitary hA : Matrix n n 𝕜)) * A =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (star (eigenvectorUnitary hA : Matrix n n 𝕜))
      := by
rw [←spectral_theorem1, mul_assoc, (Matrix.mem_unitaryGroup_iff).mp (eigenvectorUnitary hA).2,
     mul_one]

/-- A nonzero Hermitian matrix has an eigenvector with nonzero eigenvalue. -/
lemma exists_eigenvector_of_ne_zero (hA : IsHermitian A) (h_ne : A ≠ 0) :
    ∃ (v : n → 𝕜) (t : ℝ), t ≠ 0 ∧ v ≠ 0 ∧ A *ᵥ v = t • v := by
  classical
  have : hA.eigenvalues ≠ 0 := by
    contrapose! h_ne
    have := hA.spectral_theorem2
    rwa [h_ne, Pi.comp_zero, RCLike.ofReal_zero, (by rfl : Function.const n (0 : 𝕜) = fun _ ↦ 0),
      diagonal_zero, mul_zero, zero_mul] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
  exact ⟨_, _, hi, hA.eigenvectorBasis.orthonormal.ne_zero i, hA.mulVec_eigenvectorBasis i⟩

/-- The determinant of a hermitian matrix is the product of its eigenvalues. -/
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
  apply mul_left_cancel₀ (det_ne_zero_of_left_inverse (A := star (eigenvectorUnitary hA).1) (B := (eigenvectorUnitary hA).1) ((Matrix.mem_unitaryGroup_iff).mp (eigenvectorUnitary hA).2))
  rw [←det_mul, spectral_theorem3, det_mul, mul_comm, det_diagonal]
  simp_rw [Function.comp_apply]

/-- rank of a hermitian matrix is the rank of after diagonalization by the eigenvector matrix -/
lemma rank_eq_rank_diagonal : A.rank = (Matrix.diagonal hA.eigenvalues).rank := by
  conv_lhs => rw [hA.spectral_theorem2]
  have hG : (hA.eigenvectorUnitary.1) * (star (hA.eigenvectorUnitary.1)) = 1 := by
          simp only [hA.eigenvectorUnitary.2, unitary.mul_star_self_of_mem]
  have hE := isUnit_det_of_right_inverse hG
  have hE1 := isUnit_det_of_left_inverse hG
  simp only [rank_mul_eq_right_of_isUnit_det (A := hA.eigenvectorUnitary.1)
      (B := star (hA.eigenvectorUnitary.1)) hE, rank_mul_eq_left_of_isUnit_det
      (B := hA.eigenvectorUnitary.1) (A := star (hA.eigenvectorUnitary.1)) hE1,
      rank_diagonal, Function.comp_apply, ne_eq, algebraMap.lift_map_eq_zero_iff]
  sorry --not sure how to finish this one!


/-- rank of a hermitian matrix is the number of nonzero eigenvalues of the hermitian matrix -/
lemma rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := by
  rw [rank_eq_rank_diagonal hA, Matrix.rank_diagonal]

--this one needs some translation work...
theorem eigenvalues_eq (i : n) :
    hA.eigenvalues i =
      RCLike.re (star (hA.eigenvectorUnitaryᵀ i) ⬝ᵥ A *ᵥ hA.eigenvectorUnitaryᵀ i) := by
  have := hA.spectral_theorem1
  rw [← @Matrix.mul_inv_eq_iff_eq_mul_of_invertible (A := hA.eigenvectorMatrixInv)] at this
  have := congr_arg RCLike.re (congr_fun (congr_fun this i) i)
  rw [diagonal_apply_eq, Function.comp_apply, RCLike.ofReal_re,
    inv_eq_left_inv hA.eigenvectorMatrix_mul_inv, ← conjTranspose_eigenvectorMatrix, mul_mul_apply]
    at this
  exact this.symm
#align matrix.is_hermitian.eigenvalues_eq Matrix.IsHermitian.eigenvalues_eq

#exit


/-- The columns of `Matrix.IsHermitian.eigenVectorMatrix` form the basis-/
theorem transpose_eigenvectorMatrix_apply (i : n) :
    hA.eigenvectorMatrixᵀ i = hA.eigenvectorBasis i :=
  funext fun j => eigenvectorMatrix_apply hA j i


theorem conjTranspose_eigenvectorMatrixInv : hA.eigenvectorMatrixInvᴴ = hA.eigenvectorMatrix := by
  ext i j
  rw [conjTranspose_apply, eigenvectorMatrixInv_apply, eigenvectorMatrix_apply, star_star]
#align matrix.is_hermitian.conj_transpose_eigenvector_matrix_inv Matrix.IsHermitian.conjTranspose_eigenvectorMatrixInv

theorem conjTranspose_eigenvectorMatrix : hA.eigenvectorMatrixᴴ = hA.eigenvectorMatrixInv := by
  rw [← conjTranspose_eigenvectorMatrixInv, conjTranspose_conjTranspose]
#align matrix.is_hermitian.conj_transpose_eigenvector_matrix Matrix.IsHermitian.conjTranspose_eigenvectorMatrix



end DecidableEq



end IsHermitian

end Matrix
