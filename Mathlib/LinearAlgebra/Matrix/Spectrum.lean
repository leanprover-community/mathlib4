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

variable {𝕜 : Type*} [IsROrC 𝕜] [DecidableEq 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

variable {A : Matrix n n 𝕜}

def vn : ℕ := (Fintype.card n)

open scoped Matrix

open scoped BigOperators

namespace IsHermitian

variable (hA : A.IsHermitian)

/-- The eigenvalues of a hermitian matrix, indexed by `Fin (Fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : Fin (Fintype.card n) → ℝ :=
  (isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace
#align matrix.is_hermitian.eigenvalues₀ Matrix.IsHermitian.eigenvalues₀

noncomputable def xeigenvalues : Fin (Fintype.card n) → ℝ :=
  (isHermitian_iff_isSymmetric.1 hA).xeigenvalues finrank_euclideanSpace

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ := fun i =>
  hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
#align matrix.is_hermitian.eigenvalues Matrix.IsHermitian.eigenvalues

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix such that the
associated eigenvalues are sorted -/
noncomputable def xeigenvectorBasis :
    OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n) :=
  ((isHermitian_iff_isSymmetric.1 hA).xeigenvectorBasis finrank_euclideanSpace)

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  ((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))
#align matrix.is_hermitian.eigenvector_basis Matrix.IsHermitian.eigenvectorBasis

/-- A matrix whose columns are an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def xeigenvectorMatrix : Matrix n (Fin (Fintype.card n)) 𝕜 :=
  (PiLp.basisFun _ 𝕜 n).toMatrix (xeigenvectorBasis hA).toBasis

/-- A matrix whose columns are an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorMatrix : Matrix n n 𝕜 :=
  (PiLp.basisFun _ 𝕜 n).toMatrix (eigenvectorBasis hA).toBasis
#align matrix.is_hermitian.eigenvector_matrix Matrix.IsHermitian.eigenvectorMatrix

/-- The inverse of `eigenvectorMatrix` -/
noncomputable def xeigenvectorMatrixInv : Matrix (Fin (Fintype.card n)) n 𝕜 :=
  (xeigenvectorBasis hA).toBasis.toMatrix (PiLp.basisFun _ 𝕜 n)

/-- The inverse of `eigenvectorMatrix` -/
noncomputable def eigenvectorMatrixInv : Matrix n n 𝕜 :=
  (eigenvectorBasis hA).toBasis.toMatrix (PiLp.basisFun _ 𝕜 n)
#align matrix.is_hermitian.eigenvector_matrix_inv Matrix.IsHermitian.eigenvectorMatrixInv

theorem xeigenvectorMatrix_mul_inv : hA.xeigenvectorMatrix * hA.xeigenvectorMatrixInv = 1 := by
  apply Basis.toMatrix_mul_toMatrix_flip

theorem eigenvectorMatrix_mul_inv : hA.eigenvectorMatrix * hA.eigenvectorMatrixInv = 1 := by
  apply Basis.toMatrix_mul_toMatrix_flip
#align matrix.is_hermitian.eigenvector_matrix_mul_inv Matrix.IsHermitian.eigenvectorMatrix_mul_inv

-- noncomputable instance : Invertible hA.xeigenvectorMatrixInv :=
--   invertibleOfLeftInverse _ _ hA.xeigenvectorMatrix_mul_inv

noncomputable instance : Invertible hA.eigenvectorMatrixInv :=
  invertibleOfLeftInverse _ _ hA.eigenvectorMatrix_mul_inv

noncomputable instance : Invertible hA.eigenvectorMatrix :=
  invertibleOfRightInverse _ _ hA.eigenvectorMatrix_mul_inv

theorem xeigenvectorMatrix_apply (i: n)(j : Fin (vn)) : hA.xeigenvectorMatrix i j = hA.xeigenvectorBasis j i := by
  simp_rw [xeigenvectorMatrix, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    PiLp.basisFun_repr]

theorem eigenvectorMatrix_apply (i j : n) : hA.eigenvectorMatrix i j = hA.eigenvectorBasis j i := by
  simp_rw [eigenvectorMatrix, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    PiLp.basisFun_repr]
#align matrix.is_hermitian.eigenvector_matrix_apply Matrix.IsHermitian.eigenvectorMatrix_apply

/-- The columns of `Matrix.IsHermitian.eigenVectorMatrix` form the basis-/
theorem xtranspose_eigenvectorMatrix_apply (i : Fin (vn)) :
    hA.xeigenvectorMatrixᵀ i = hA.xeigenvectorBasis i :=
  funext <| fun j => xeigenvectorMatrix_apply hA j i

/-- The columns of `Matrix.IsHermitian.eigenVectorMatrix` form the basis-/
theorem transpose_eigenvectorMatrix_apply (i : n) :
    hA.eigenvectorMatrixᵀ i = hA.eigenvectorBasis i :=
  funext <| fun j => eigenvectorMatrix_apply hA j i

theorem xeigenvectorMatrixInv_apply (i : Fin (vn))(j : n) :
    hA.xeigenvectorMatrixInv i j = star (hA.xeigenvectorBasis i j) := by
  rw [xeigenvectorMatrixInv, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, PiLp.basisFun_apply, PiLp.equiv_symm_single,
    EuclideanSpace.inner_single_right, one_mul, IsROrC.star_def]

theorem eigenvectorMatrixInv_apply (i j : n) :
    hA.eigenvectorMatrixInv i j = star (hA.eigenvectorBasis i j) := by
  rw [eigenvectorMatrixInv, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, PiLp.basisFun_apply, PiLp.equiv_symm_single,
    EuclideanSpace.inner_single_right, one_mul, IsROrC.star_def]
#align matrix.is_hermitian.eigenvector_matrix_inv_apply Matrix.IsHermitian.eigenvectorMatrixInv_apply

theorem xconjTranspose_eigenvectorMatrixInv : hA.xeigenvectorMatrixInvᴴ = hA.xeigenvectorMatrix := by
  ext i j
  rw [conjTranspose_apply, xeigenvectorMatrixInv_apply, xeigenvectorMatrix_apply, star_star]

theorem conjTranspose_eigenvectorMatrixInv : hA.eigenvectorMatrixInvᴴ = hA.eigenvectorMatrix := by
  ext i j
  rw [conjTranspose_apply, eigenvectorMatrixInv_apply, eigenvectorMatrix_apply, star_star]
#align matrix.is_hermitian.conj_transpose_eigenvector_matrix_inv Matrix.IsHermitian.conjTranspose_eigenvectorMatrixInv

theorem xconjTranspose_eigenvectorMatrix : hA.xeigenvectorMatrixᴴ = hA.xeigenvectorMatrixInv := by
  rw [← xconjTranspose_eigenvectorMatrixInv, conjTranspose_conjTranspose]

theorem conjTranspose_eigenvectorMatrix : hA.eigenvectorMatrixᴴ = hA.eigenvectorMatrixInv := by
  rw [← conjTranspose_eigenvectorMatrixInv, conjTranspose_conjTranspose]
#align matrix.is_hermitian.conj_transpose_eigenvector_matrix Matrix.IsHermitian.conjTranspose_eigenvectorMatrix

/-- *Diagonalization theorem*, *spectral theorem* for matrices; A hermitian matrix can be
diagonalized by a change of basis.

For the spectral theorem on linear maps, see
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`. -/
theorem spectral_theorem :
    hA.eigenvectorMatrixInv * A = diagonal ((↑) ∘ hA.eigenvalues) * hA.eigenvectorMatrixInv := by
  rw [eigenvectorMatrixInv]
  rw [PiLp.basis_toMatrix_basisFun_mul]
  ext i j
  have := isHermitian_iff_isSymmetric.1 hA
  convert this.eigenvectorBasis_apply_self_apply finrank_euclideanSpace (EuclideanSpace.single j 1)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) using 1
  · dsimp only [EuclideanSpace.single, toEuclideanLin_piLp_equiv_symm, toLin'_apply,
      Matrix.of_apply, IsHermitian.eigenvectorBasis]
    simp_rw [mulVec_single, mul_one, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_reindex]
    rfl
  · simp only [diagonal_mul, (· ∘ ·), eigenvalues]
    rw [eigenvectorBasis, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_reindex, eigenvalues₀, PiLp.basisFun_apply, PiLp.equiv_symm_single]
#align matrix.is_hermitian.spectral_theorem Matrix.IsHermitian.spectral_theorem

variable (p : ENNReal)

nonrec theorem xbasis_toMatrix_basisFun_mul (b : Basis (Fin (Fintype.card n)) 𝕜 (PiLp p fun _ : n => 𝕜))
    (A : Matrix n n 𝕜) :
    b.toMatrix (PiLp.basisFun _ _ _) * A =
      Matrix.of fun i j => b.repr ((PiLp.equiv _ _).symm (Aᵀ j)) i := by sorry
  -- have := basis_toMatrix_basisFun_mul (b.map (PiLp.linearEquiv _ 𝕜 _)) A
  -- simp_rw [← PiLp.basisFun_map p, Basis.map_repr, LinearEquiv.trans_apply,
  --   WithLp.linearEquiv_symm_apply, Basis.toMatrix_map, Function.comp, Basis.map_apply,
  --   LinearEquiv.symm_apply_apply] at this
  -- exact this

theorem xspectral_theorem :
    hA.xeigenvectorMatrixInv * A = diagonal ((↑) ∘ hA.xeigenvalues) * hA.xeigenvectorMatrixInv := by
  rw [xeigenvectorMatrixInv]
  rw [xbasis_toMatrix_basisFun_mul]
  ext i j
  have := isHermitian_iff_isSymmetric.1 hA
  convert this.xeigenvectorBasis_apply_self_apply finrank_euclideanSpace
    (EuclideanSpace.single j 1) i
  · dsimp only [EuclideanSpace.single, toEuclideanLin_piLp_equiv_symm, toLin'_apply,
      Matrix.of_apply, IsHermitian.xeigenvectorBasis]
    simp_rw [mulVec_single, mul_one, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_reindex]
    rfl

  · simp only [diagonal_mul, (· ∘ ·), xeigenvalues]
    rw [xeigenvectorBasis, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      PiLp.basisFun_apply, PiLp.equiv_symm_single]

theorem eigenvalues_eq (i : n) :
    hA.eigenvalues i =
      IsROrC.re (star (hA.eigenvectorMatrixᵀ i) ⬝ᵥ A.mulVec (hA.eigenvectorMatrixᵀ i)) := by
  have := hA.spectral_theorem
  rw [← @Matrix.mul_inv_eq_iff_eq_mul_of_invertible (A := hA.eigenvectorMatrixInv)] at this
  have := congr_arg IsROrC.re (congr_fun (congr_fun this i) i)
  rw [diagonal_apply_eq, Function.comp_apply, IsROrC.ofReal_re,
    inv_eq_left_inv hA.eigenvectorMatrix_mul_inv, ← conjTranspose_eigenvectorMatrix, mul_mul_apply]
    at this
  exact this.symm
#align matrix.is_hermitian.eigenvalues_eq Matrix.IsHermitian.eigenvalues_eq

/-- The determinant of a hermitian matrix is the product of its eigenvalues. -/
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
  apply mul_left_cancel₀ (det_ne_zero_of_left_inverse (eigenvectorMatrix_mul_inv hA))
  rw [← det_mul, spectral_theorem, det_mul, mul_comm, det_diagonal]
  simp_rw [Function.comp_apply]
#align matrix.is_hermitian.det_eq_prod_eigenvalues Matrix.IsHermitian.det_eq_prod_eigenvalues

/-- *spectral theorem* (Alternate form for convenience) A hermitian matrix can be can be
replaced by a diagonal matrix sandwiched between the eigenvector matrices. This alternate form
allows direct rewriting of A since: $ A = V D V⁻¹$ -/
lemma spectral_theorem' :
    A = hA.eigenvectorMatrix * diagonal ((↑) ∘ hA.eigenvalues) * hA.eigenvectorMatrixInv := by
  simpa [ ← Matrix.mul_assoc, hA.eigenvectorMatrix_mul_inv, Matrix.one_mul] using
    congr_arg (hA.eigenvectorMatrix * ·) hA.spectral_theorem

lemma xspectral_theorem' :
    A = hA.xeigenvectorMatrix * diagonal ((↑) ∘ hA.xeigenvalues) * hA.xeigenvectorMatrixInv := by
  simpa [ ← Matrix.mul_assoc, hA.xeigenvectorMatrix_mul_inv, Matrix.one_mul] using
    congr_arg (hA.xeigenvectorMatrix * ·) hA.xspectral_theorem


/-- rank of a hermitian matrix is the rank of after diagonalization by the eigenvector matrix -/
lemma rank_eq_rank_diagonal : A.rank = (Matrix.diagonal hA.eigenvalues).rank := by
  conv_lhs => rw [hA.spectral_theorem']
  have hE := isUnit_det_of_invertible (hA.eigenvectorMatrix)
  have hiE := isUnit_det_of_invertible (hA.eigenvectorMatrixInv)
  simp only [rank_mul_eq_right_of_isUnit_det hA.eigenvectorMatrix _ hE,
    rank_mul_eq_left_of_isUnit_det hA.eigenvectorMatrixInv _ hiE,
    rank_diagonal, Function.comp_apply, ne_eq, algebraMap.lift_map_eq_zero_iff]

/-- A sorted nonnegative list with m elements and exactly r ≤ m non-zero elemnts has the first
(m - r) elemnts as zero -/
lemma wierd (m r : ℕ) (hrm : r ≤ m) (f : Fin m → ℝ)
    (h_nonneg : ∀ (i : Fin m), 0 ≤  f i)
    (h_nz_cnt : Fintype.card { i // f i =  0} = (m -r))
    (h_sorted : Monotone f)
    (j : Fin m):
    ( j < (m - r) ) → f j = 0 := by
  intro hjm
  have hj := eq_or_lt_of_le ( h_nonneg j)
  cases' hj with hj hj
  exact hj.symm
  exfalso
  unfold Monotone at h_sorted
  have : ∃ q : Fin m, (m - r) ≤ q ∧ f q = 0 := by sorry
  obtain ⟨q , hq⟩ := this
  have hjq : j < q := by exact_mod_cast lt_of_lt_of_le hjm hq.left
  have h1 : (f q < f j) := by
    rw [hq.2]
    exact hj
  have h2 := h_sorted (le_of_lt hjq)
  apply (not_lt.2 h2) h1





#eval 0
  -- cases' r with rs
  -- · simp only [nonpos_iff_eq_zero, tsub_zero, Fin.is_lt] at hjm
  --   by_contra h
  --   apply not_nonempty_iff.2 (Fintype.card_eq_zero_iff.1 h_nz_cnt) ⟨j, h⟩
  -- · unfold Monotone at h_sorted
  --   -- by_contra h
  --   sorry






-- lemma xrank_eq_rank_diagonal : A.rank = (Matrix.diagonal hA.xeigenvalues).rank := by
--   conv_lhs => rw [hA.xspectral_theorem']
--   have hE := isUnit_det_of_invertible (hA.xeigenvectorMatrix)
--   have hiE := isUnit_det_of_invertible (hA.eigenvectorMatrixInv)
--   simp only [rank_mul_eq_right_of_isUnit_det hA.eigenvectorMatrix _ hE,
--     rank_mul_eq_left_of_isUnit_det hA.eigenvectorMatrixInv _ hiE,
--     rank_diagonal, Function.comp_apply, ne_eq, algebraMap.lift_map_eq_zero_iff]

/-- rank of a hermitian matrix is the number of nonzero eigenvalues of the hermitian matrix -/
lemma rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := by
  rw [rank_eq_rank_diagonal hA, Matrix.rank_diagonal]

end IsHermitian

end Matrix
