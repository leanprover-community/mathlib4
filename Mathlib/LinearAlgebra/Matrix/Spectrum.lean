/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.NormedSpace.Star.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

#align_import linear_algebra.matrix.spectrum from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-! # Spectral theory of hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
variable {A : Matrix n n 𝕜}

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

lemma mulVec_eigenvectorBasis (j : n) :
    A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) := by
  simpa only [eigenvectorBasis, OrthonormalBasis.reindex_apply, toEuclideanLin_apply,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
      congr(⇑$((isHermitian_iff_isSymmetric.1 hA).apply_eigenvectorBasis
        finrank_euclideanSpace ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)))

/-- The spectrum of a Hermitian matrix `A` coincides with the spectrum of `toEuclideanLin A`. -/
theorem spectrum_toEuclideanLin : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A :=
  AlgEquiv.spectrum_eq
    (AlgEquiv.trans
      ((toEuclideanCLM : Matrix n n 𝕜 ≃⋆ₐ[𝕜] EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) :
          Matrix n n 𝕜 ≃ₐ[𝕜] EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)
      (Module.End.toContinuousLinearMap (EuclideanSpace 𝕜 n)).symm)
    _

/-- Eigenvalues of a hermitian matrix A are in the ℝ spectrum of A. -/
theorem eigenvalues_mem_spectrum_real (i : n) : hA.eigenvalues i ∈ spectrum ℝ A := by
  apply spectrum.of_algebraMap_mem 𝕜
  rw [← spectrum_toEuclideanLin]
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _ |>.mem_spectrum

/-- Unitary matrix whose columns are `Matrix.IsHermitian.eigenvectorBasis`. -/
noncomputable def eigenvectorUnitary {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n]{A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    Matrix.unitaryGroup n 𝕜 :=
  ⟨(EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis,
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary (eigenvectorBasis hA)⟩
#align matrix.is_hermitian.eigenvector_matrix Matrix.IsHermitian.eigenvectorUnitary

lemma eigenvectorUnitary_coe {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    eigenvectorUnitary hA =
      (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis :=
  rfl

@[simp]
theorem eigenvectorUnitary_apply (i j : n) :
    eigenvectorUnitary hA i j = ⇑(hA.eigenvectorBasis j) i :=
  rfl
#align matrix.is_hermitian.eigenvector_matrix_apply Matrix.IsHermitian.eigenvectorUnitary_apply

theorem eigenvectorUnitary_mulVec (j : n) :
    eigenvectorUnitary hA *ᵥ Pi.single j 1 = ⇑(hA.eigenvectorBasis j) := by
  simp only [mulVec_single, eigenvectorUnitary_apply, mul_one]

theorem star_eigenvectorUnitary_mulVec (j : n) :
    (star (eigenvectorUnitary hA : Matrix n n 𝕜)) *ᵥ ⇑(hA.eigenvectorBasis j) = Pi.single j 1 := by
  rw [← eigenvectorUnitary_mulVec, mulVec_mulVec, unitary.coe_star_mul_self, one_mulVec]

/-- Unitary diagonalization of a Hermitian matrix. -/
theorem star_mul_self_mul_eq_diagonal :
    (star (eigenvectorUnitary hA : Matrix n n 𝕜)) * A * (eigenvectorUnitary hA : Matrix n n 𝕜)
      = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
  apply Matrix.toEuclideanLin.injective
  apply Basis.ext (EuclideanSpace.basisFun n 𝕜).toBasis
  intro i
  simp only [toEuclideanLin_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    WithLp.equiv_single, ← mulVec_mulVec, eigenvectorUnitary_mulVec, ← mulVec_mulVec,
    mulVec_eigenvectorBasis, Matrix.diagonal_mulVec_single, mulVec_smul,
    star_eigenvectorUnitary_mulVec, RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.equiv_symm_smul,
    WithLp.equiv_symm_single, Function.comp_apply, mul_one, WithLp.equiv_symm_single]
  apply PiLp.ext
  intro j
  simp only [PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]


/-- **Diagonalization theorem**, **spectral theorem** for matrices; A hermitian matrix can be
diagonalized by a change of basis. For the spectral theorem on linear maps, see
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`.-/
theorem spectral_theorem :
    A = (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      * (star (eigenvectorUnitary hA : Matrix n n 𝕜)) := by
  rw [← star_mul_self_mul_eq_diagonal, mul_assoc, mul_assoc,
    (Matrix.mem_unitaryGroup_iff).mp (eigenvectorUnitary hA).2, mul_one,
    ← mul_assoc, (Matrix.mem_unitaryGroup_iff).mp (eigenvectorUnitary hA).2, one_mul]
#align matrix.is_hermitian.spectral_theorem' Matrix.IsHermitian.spectral_theorem

theorem eigenvalues_eq (i : n) :
    (hA.eigenvalues i) = RCLike.re (Matrix.dotProduct (star ⇑(hA.eigenvectorBasis i))
    (A *ᵥ ⇑(hA.eigenvectorBasis i))) := by
  simp only [mulVec_eigenvectorBasis, dotProduct_smul,← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, RCLike.smul_re, hA.eigenvectorBasis.orthonormal.1 i,
    mul_one, algebraMap.coe_one, one_pow, RCLike.one_re]
#align matrix.is_hermitian.eigenvalues_eq Matrix.IsHermitian.eigenvalues_eq

/-- The determinant of a hermitian matrix is the product of its eigenvalues. -/
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
  convert congr_arg det hA.spectral_theorem
  rw [det_mul_right_comm]
  simp
#align matrix.is_hermitian.det_eq_prod_eigenvalues Matrix.IsHermitian.det_eq_prod_eigenvalues

/-- rank of a hermitian matrix is the rank of after diagonalization by the eigenvector unitary -/
lemma rank_eq_rank_diagonal : A.rank = (Matrix.diagonal hA.eigenvalues).rank := by
  conv_lhs => rw [hA.spectral_theorem, ← unitary.coe_star]
  simp [-isUnit_iff_ne_zero, -unitary.coe_star, rank_diagonal]
#align matrix.is_hermitian.rank_eq_rank_diagonal Matrix.IsHermitian.rank_eq_rank_diagonal

/-- rank of a hermitian matrix is the number of nonzero eigenvalues of the hermitian matrix -/
lemma rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := by
  rw [rank_eq_rank_diagonal hA, Matrix.rank_diagonal]
#align matrix.is_hermitian.rank_eq_card_non_zero_eigs Matrix.IsHermitian.rank_eq_card_non_zero_eigs

end DecidableEq

/-- A nonzero Hermitian matrix has an eigenvector with nonzero eigenvalue. -/
lemma exists_eigenvector_of_ne_zero (hA : IsHermitian A) (h_ne : A ≠ 0) :
    ∃ (v : n → 𝕜) (t : ℝ), t ≠ 0 ∧ v ≠ 0 ∧ A *ᵥ v = t • v := by
  classical
  have : hA.eigenvalues ≠ 0 := by
    contrapose! h_ne
    have := hA.spectral_theorem
    rwa [h_ne, Pi.comp_zero, RCLike.ofReal_zero, (by rfl : Function.const n (0 : 𝕜) = fun _ ↦ 0),
      diagonal_zero, mul_zero, zero_mul] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
  exact ⟨_, _, hi, hA.eigenvectorBasis.orthonormal.ne_zero i, hA.mulVec_eigenvectorBasis i⟩
#align matrix.is_hermitian.exists_eigenvector_of_ne_zero Matrix.IsHermitian.exists_eigenvector_of_ne_zero

/-- # Reduced Spectral Theorem
For A hermitian matrix A with rank A.rank ≤ n, we can eliminate the zero eigenvalues and their
corresponding eigenvectors from the (alternate) spectral theroem. As such the matrix A can be written as:
$$A = V₁ D V₁ᴴ$$
where
V₁ : n × r is the matrix of eigenvector with non-zero associated eigenvalues.
D is r × r is the diagonal matrix containing only non-zero eigenvalues.
with r = A.rank being the rank of the matrix -/
noncomputable def fin_rank_equiv_eigs_ne_zero : {i // hA.eigenvalues i ≠ 0} ≃ Fin (A.rank) :=
  Fintype.equivFinOfCardEq (rank_eq_card_non_zero_eigs _).symm

noncomputable def fin_size_sub_rank_equiv_eigs_eq_zero :
    {i // ¬ hA.eigenvalues i ≠ 0} ≃ Fin (Fintype.card n - A.rank) := by
  apply Fintype.equivFinOfCardEq
  rw [Fintype.card_subtype_compl, rank_eq_card_non_zero_eigs]

noncomputable def fin_size_equiv_eigs :
    {i // hA.eigenvalues i ≠ 0} ⊕ {i // ¬hA.eigenvalues i ≠ 0}  ≃ n := by
  apply  Fintype.equivOfCardEq
  rw [Fintype.card_sum, ← rank_eq_card_non_zero_eigs, Fintype.card_subtype_compl, ←
    rank_eq_card_non_zero_eigs, ← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
  exact Matrix.rank_le_card_width _

noncomputable def fin_size_equiv_rank_sum_compl :
    Fin (A.rank) ⊕ Fin (Fintype.card n - A.rank) ≃ n := by
  let s1 : {i // hA.eigenvalues i ≠ 0} ⊕ {i // ¬hA.eigenvalues i ≠ 0} ≃
      Fin (A.rank) ⊕ Fin (Fintype.card n - A.rank) :=
    Equiv.sumCongr (fin_rank_equiv_eigs_ne_zero _) (fin_size_sub_rank_equiv_eigs_eq_zero _)
  apply Equiv.trans s1.symm (fin_size_equiv_eigs _)


end IsHermitian

end Matrix

/-The following were removed as a result of the refactor, since they either were
unused in the library, followed as immediate consequences of, or were replaced by
above results (e.g. results about inverses don't need replacement because their unitary
analogues have replaced them).-/

#noalign Matrix.IsHermitian.eigenvector_matrix_inv
#noalign matrix.is_hermitian.eigenvector_matrix_mul_inv
#noalign matrix.is_hermitian.eigenvector_matrix_inv_apply
#noalign matrix.is_hermitian.conj_transpose_eigenvector_matrix_inv
#noalign matrix.is_hermitian.conj_transpose_eigenvector_matrix
#noalign matrix.is_hermitian.spectral_theorem
