/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Spectral theory of hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem -/

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

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ := fun i =>
  hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  ((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))

lemma mulVec_eigenvectorBasis (j : n) :
    A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) := by
  simpa only [eigenvectorBasis, OrthonormalBasis.reindex_apply, toEuclideanLin_apply,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
      congr(⇑$((isHermitian_iff_isSymmetric.1 hA).apply_eigenvectorBasis
        finrank_euclideanSpace ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)))

/-- The spectrum of a Hermitian matrix `A` coincides with the spectrum of `toEuclideanLin A`. -/
theorem spectrum_toEuclideanLin : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A :=
  AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (PiLp.basisFun 2 𝕜 n)) _

/-- Eigenvalues of a hermitian matrix A are in the ℝ spectrum of A. -/
theorem eigenvalues_mem_spectrum_real (i : n) : hA.eigenvalues i ∈ spectrum ℝ A := by
  apply spectrum.of_algebraMap_mem 𝕜
  rw [← spectrum_toEuclideanLin]
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _ |>.mem_spectrum

/-- Unitary matrix whose columns are `Matrix.IsHermitian.eigenvectorBasis`. -/
noncomputable def eigenvectorUnitary {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n] {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    Matrix.unitaryGroup n 𝕜 :=
  ⟨(EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis,
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary (eigenvectorBasis hA)⟩

lemma eigenvectorUnitary_coe {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    eigenvectorUnitary hA =
      (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis :=
  rfl

@[simp]
theorem eigenvectorUnitary_transpose_apply (j : n) :
    (eigenvectorUnitary hA)ᵀ j = ⇑(hA.eigenvectorBasis j) :=
  rfl

@[simp]
theorem eigenvectorUnitary_apply (i j : n) :
    eigenvectorUnitary hA i j = ⇑(hA.eigenvectorBasis j) i :=
  rfl

theorem eigenvectorUnitary_mulVec (j : n) :
    eigenvectorUnitary hA *ᵥ Pi.single j 1 = ⇑(hA.eigenvectorBasis j) := by
  simp_rw [mulVec_single_one, eigenvectorUnitary_transpose_apply]

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
    EuclideanSpace.ofLp_single, ← mulVec_mulVec, eigenvectorUnitary_mulVec, ← mulVec_mulVec,
    mulVec_eigenvectorBasis, Matrix.diagonal_mulVec_single, mulVec_smul,
    star_eigenvectorUnitary_mulVec, RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.toLp_smul,
    EuclideanSpace.toLp_single, Function.comp_apply, mul_one]
  apply PiLp.ext
  intro j
  simp only [PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- **Diagonalization theorem**, **spectral theorem** for matrices; A hermitian matrix can be
diagonalized by a change of basis. For the spectral theorem on linear maps, see
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`. -/
theorem spectral_theorem :
    A = (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      * (star (eigenvectorUnitary hA : Matrix n n 𝕜)) := by
  rw [← star_mul_self_mul_eq_diagonal, mul_assoc, mul_assoc,
    (Matrix.mem_unitaryGroup_iff).mp (eigenvectorUnitary hA).2, mul_one,
    ← mul_assoc, (Matrix.mem_unitaryGroup_iff).mp (eigenvectorUnitary hA).2, one_mul]

theorem eigenvalues_eq (i : n) :
    (hA.eigenvalues i) = RCLike.re (dotProduct (star ⇑(hA.eigenvectorBasis i))
    (A *ᵥ ⇑(hA.eigenvectorBasis i))) := by
  rw [dotProduct_comm]
  simp only [mulVec_eigenvectorBasis, smul_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, RCLike.smul_re, hA.eigenvectorBasis.orthonormal.1 i,
    mul_one, algebraMap.coe_one, one_pow, RCLike.one_re]

/-- The determinant of a hermitian matrix is the product of its eigenvalues. -/
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
  convert congr_arg det hA.spectral_theorem
  rw [det_mul_right_comm]
  simp

/-- rank of a hermitian matrix is the rank of after diagonalization by the eigenvector unitary -/
lemma rank_eq_rank_diagonal : A.rank = (Matrix.diagonal hA.eigenvalues).rank := by
  conv_lhs => rw [hA.spectral_theorem, ← unitary.coe_star]
  simp [-isUnit_iff_ne_zero, -unitary.coe_star, rank_diagonal]

/-- rank of a hermitian matrix is the number of nonzero eigenvalues of the hermitian matrix -/
lemma rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := by
  rw [rank_eq_rank_diagonal hA, Matrix.rank_diagonal]

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

end IsHermitian

end Matrix

/-The following were removed as a result of the refactor, since they either were
unused in the library, followed as immediate consequences of, or were replaced by
above results (e.g. results about inverses don't need replacement because their unitary
analogues have replaced them). -/
