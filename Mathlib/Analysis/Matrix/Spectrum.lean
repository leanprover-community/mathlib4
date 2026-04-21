/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Spectral theory of Hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem -/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open WithLp

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
variable {A B : Matrix n n 𝕜}

lemma finite_real_spectrum [DecidableEq n] : (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap 𝕜]
  exact A.finite_spectrum.preimage (FaithfulSMul.algebraMap_injective ℝ 𝕜).injOn

instance [DecidableEq n] : Finite (spectrum ℝ A) := A.finite_real_spectrum

/-- The spectrum of a matrix `A` coincides with the spectrum of `toLpLin p p A`. -/
theorem spectrum_toLpLin [DecidableEq n] (p : ENNReal) :
    spectrum 𝕜 (toLpLin p p A) = spectrum 𝕜 A :=
  AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (PiLp.basisFun p 𝕜 n)) _

/-- The spectrum of a matrix `A` coincides with the spectrum of `toEuclideanLin A`. -/
@[deprecated spectrum_toLpLin (since := "2026-01-21")]
theorem spectrum_toEuclideanLin [DecidableEq n] : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A :=
  spectrum_toLpLin 2

namespace IsHermitian

section DecidableEq

variable [DecidableEq n]
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

/-- The eigenvalues of a Hermitian matrix, indexed by `Fin (Fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : Fin (Fintype.card n) → ℝ :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace

lemma eigenvalues₀_antitone : Antitone hA.eigenvalues₀ :=
  LinearMap.IsSymmetric.eigenvalues_antitone ..

/-- The eigenvalues of a Hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ := fun i =>
  hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i

/-- A choice of an orthonormal basis of eigenvectors of a Hermitian matrix. -/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))

lemma mulVec_eigenvectorBasis (j : n) :
    A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) := by
  simpa only [eigenvectorBasis, OrthonormalBasis.reindex_apply, toLpLin_apply,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
      congr(⇑$((isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis
        finrank_euclideanSpace ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)))

/-- Eigenvalues of a Hermitian matrix A are in the ℝ spectrum of A. -/
theorem eigenvalues_mem_spectrum_real (i : n) : hA.eigenvalues i ∈ spectrum ℝ A := by
  apply spectrum.of_algebraMap_mem 𝕜
  rw [← Matrix.spectrum_toLpLin 2]
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
theorem eigenvectorUnitary_col_eq (j : n) :
    Matrix.col (eigenvectorUnitary hA) j = ⇑(hA.eigenvectorBasis j) :=
  rfl

@[simp]
theorem eigenvectorUnitary_apply (i j : n) :
    eigenvectorUnitary hA i j = ⇑(hA.eigenvectorBasis j) i :=
  rfl

theorem eigenvectorUnitary_mulVec (j : n) :
    eigenvectorUnitary hA *ᵥ Pi.single j 1 = ⇑(hA.eigenvectorBasis j) := by
  simp_rw [mulVec_single_one, eigenvectorUnitary_col_eq]

theorem star_eigenvectorUnitary_mulVec (j : n) :
    (star (eigenvectorUnitary hA : Matrix n n 𝕜)) *ᵥ ⇑(hA.eigenvectorBasis j) = Pi.single j 1 := by
  rw [← eigenvectorUnitary_mulVec, mulVec_mulVec, Unitary.coe_star_mul_self, one_mulVec]

open Unitary

/-- Unitary diagonalization of a Hermitian matrix. -/
theorem conjStarAlgAut_star_eigenvectorUnitary :
    conjStarAlgAut 𝕜 _ (star hA.eigenvectorUnitary) A =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
  apply Matrix.toEuclideanLin.injective <| (EuclideanSpace.basisFun n 𝕜).toBasis.ext fun i ↦ ?_
  simp only [conjStarAlgAut_star_apply, toLpLin_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, PiLp.ofLp_single, ← mulVec_mulVec,
    eigenvectorUnitary_mulVec, ← mulVec_mulVec, mulVec_eigenvectorBasis,
    Matrix.diagonal_mulVec_single, mulVec_smul, star_eigenvectorUnitary_mulVec,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.toLp_smul, PiLp.toLp_single,
    Function.comp_apply, mul_one]
  apply PiLp.ext fun j ↦ ?_
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

@[deprecated (since := "2025-11-06")] alias star_mul_self_mul_eq_diagonal :=
  conjStarAlgAut_star_eigenvectorUnitary

/-- **Diagonalization theorem**, **spectral theorem** for matrices; A Hermitian matrix can be
diagonalized by a change of basis. For the spectral theorem on linear maps, see
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`. -/
theorem spectral_theorem :
    A = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
  rw [← conjStarAlgAut_star_eigenvectorUnitary, ← conjStarAlgAut_mul_apply]
  simp

theorem eigenvalues_eq (i : n) :
    (hA.eigenvalues i) = RCLike.re (dotProduct (star ⇑(hA.eigenvectorBasis i))
    (A *ᵥ ⇑(hA.eigenvectorBasis i))) := by
  rw [dotProduct_comm]
  simp only [mulVec_eigenvectorBasis, smul_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, RCLike.smul_re, hA.eigenvectorBasis.orthonormal.1 i,
    mul_one, algebraMap.coe_one, one_pow, RCLike.one_re]

open Polynomial in
lemma charpoly_eq : A.charpoly = ∏ i, (X - C (hA.eigenvalues i : 𝕜)) := by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

lemma roots_charpoly_eq_eigenvalues :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
  rw [hA.charpoly_eq, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

lemma roots_charpoly_eq_eigenvalues₀ :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues₀) Finset.univ.val := by
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [← Multiset.map_map, eigenvalues, ← Function.comp_apply (f := hA.eigenvalues₀)]
  simp

lemma sort_roots_charpoly_eq_eigenvalues₀ :
    (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) = List.ofFn hA.eigenvalues₀ := by
  simp_rw [hA.roots_charpoly_eq_eigenvalues₀, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact (eigenvalues₀_antitone hA).sortedGE_ofFn

lemma eigenvalues_eq_eigenvalues_iff :
    hA.eigenvalues = hB.eigenvalues ↔ A.charpoly = B.charpoly := by
  constructor <;> intro h
  · rw [hA.charpoly_eq, hB.charpoly_eq, h]
  · suffices hA.eigenvalues₀ = hB.eigenvalues₀ by unfold eigenvalues; rw [this]
    simp_rw [← List.ofFn_inj, ← sort_roots_charpoly_eq_eigenvalues₀, h]

theorem splits_charpoly (hA : A.IsHermitian) : A.charpoly.Splits :=
  Polynomial.splits_iff_card_roots.mpr (by simp [hA.roots_charpoly_eq_eigenvalues])

/-- The determinant of a Hermitian matrix is the product of its eigenvalues. -/
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
  simp [det_eq_prod_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

/-- rank of a Hermitian matrix is the rank of after diagonalization by the eigenvector unitary -/
lemma rank_eq_rank_diagonal : A.rank = (diagonal hA.eigenvalues).rank := by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, ← coe_star]
  simp [-isUnit_iff_ne_zero, -coe_star, rank_diagonal]

/-- rank of a Hermitian matrix is the number of nonzero eigenvalues of the Hermitian matrix -/
lemma rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := by
  rw [rank_eq_rank_diagonal hA, Matrix.rank_diagonal]

/-- The spectrum of a Hermitian matrix is the range of its eigenvalues under `RCLike.ofReal`. -/
theorem spectrum_eq_image_range :
    spectrum 𝕜 A = RCLike.ofReal '' Set.range hA.eigenvalues := Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem]
  simp

/-- The `ℝ`-spectrum of a Hermitian matrix over `RCLike` field is the range of the eigenvalue
function. -/
theorem spectrum_real_eq_range_eigenvalues :
    spectrum ℝ A = Set.range hA.eigenvalues := Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem, ← spectrum.algebraMap_mem_iff 𝕜]
  simp

/-- The eigenvalues of a Hermitian matrix `A` are all zero iff `A = 0`. -/
theorem eigenvalues_eq_zero_iff :
    hA.eigenvalues = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by ext; simp [h, eigenvalues_eq]⟩
  rw [hA.spectral_theorem, h, Pi.comp_zero, RCLike.ofReal_zero, Function.const_zero,
    Pi.zero_def, diagonal_zero, map_zero]

end DecidableEq

/-- A nonzero Hermitian matrix has an eigenvector with nonzero eigenvalue. -/
lemma exists_eigenvector_of_ne_zero (hA : IsHermitian A) (h_ne : A ≠ 0) :
    ∃ (v : n → 𝕜) (t : ℝ), t ≠ 0 ∧ v ≠ 0 ∧ A *ᵥ v = t • v := by
  classical
  have : hA.eigenvalues ≠ 0 := by
    contrapose h_ne
    have := hA.spectral_theorem
    rwa [h_ne, Pi.comp_zero, RCLike.ofReal_zero, (by rfl : Function.const n (0 : 𝕜) = fun _ ↦ 0),
      diagonal_zero, map_zero] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
  exact ⟨_, _, hi, (ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i,
    hA.mulVec_eigenvectorBasis i⟩

theorem trace_eq_sum_eigenvalues [DecidableEq n] (hA : A.IsHermitian) :
    A.trace = ∑ i, (hA.eigenvalues i : 𝕜) := by
  simp [trace_eq_sum_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

end IsHermitian

end Matrix
