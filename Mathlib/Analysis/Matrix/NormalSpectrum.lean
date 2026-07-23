/-
Copyright (c) 2026 Judson Pereira de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judson Pereira de Moura
-/
module

public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NoncommRing

/-! # Spectral theorem for normal matrices

`Matrix.IsHermitian.spectral_theorem` in `Mathlib/Analysis/Matrix/Spectrum.lean` diagonalizes a
*Hermitian* matrix by a unitary change of basis. This file extends that to *normal* matrices
over `ℂ` (`IsStarNormal M`, i.e. `Mᴴ * M = M * Mᴴ`): every normal complex matrix is unitarily
similar to a diagonal matrix, `M = U * diagonal μ * Uᴴ`.

Unlike the Hermitian case, this is specific to `ℂ` (algebraically closed): a real normal matrix —
e.g. a planar rotation — is normal but is not orthogonally diagonalizable over `ℝ`.

## Main definitions

* `Matrix.normalEigenvectorBasis`: a choice of orthonormal eigenbasis of a normal matrix.
* `Matrix.normalEigenvalues`: the associated complex eigenvalues.
* `Matrix.normalEigenvectorUnitary`: the unitary matrix whose columns are that eigenbasis.

## Main results

* `Matrix.mulVec_normalEigenvectorBasis`: `M *ᵥ B j = μ j • B j` (the eigen equation).
* `Matrix.spectral_theorem_of_isStarNormal`: `M = U * diagonal μ * Uᴴ`.
* `Matrix.exists_isUnitary_conj_diagonal_of_isStarNormal`: the existential form (forward direction).
* `Matrix.isStarNormal_of_isUnitary_conj_diagonal`: the converse, a unitarily-diagonalizable
  matrix is normal.
* `Matrix.isStarNormal_iff_exists_isUnitary_conj_diagonal`: the full `iff`.
* `Matrix.det_eq_prod_normalEigenvalues` / `trace_eq_sum_normalEigenvalues`: determinant and trace
  as the product and sum of the eigenvalues.
* `Matrix.charpoly_eq_prod_normalEigenvalues`: the characteristic polynomial as `∏ (X - μ i)`.
* `Matrix.spectrum_eq_range_normalEigenvalues`: the spectrum as the range of the eigenvalues.
* `Matrix.rank_eq_card_normalEigenvalues_ne_zero`: the rank as the count of nonzero eigenvalues.

## Implementation notes

The proof uses the decomposition `M = ℜ M + i • ℑ M` into the `realPart` and `imaginaryPart` of `M`,
both self-adjoint (hence Hermitian as matrices). Normality of `M` is exactly
`Commute (ℜ M) (ℑ M)` (`isStarNormal_iff_commute_realPart_imaginaryPart`), so they are *commuting
symmetric operators* and the space splits as an internal direct sum of their *joint* eigenspaces
(`LinearMap.IsSymmetric.directSum_isInternal_of_commute`). An orthonormal basis subordinate to that
decomposition diagonalizes both simultaneously, hence `M`.

The bundled API (`normalEigenvectorBasis`/`normalEigenvalues`/`normalEigenvectorUnitary`) mirrors
the Hermitian API (`Matrix.IsHermitian.eigenvectorBasis`/`eigenvalues`/`eigenvectorUnitary`).
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)

open Module.End

private lemma realPart_toEuclideanLin_isSymmetric :
    (realPart M : Matrix n n ℂ).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (selfAdjoint.mem_iff.mp (realPart M).2)

private lemma imaginaryPart_toEuclideanLin_isSymmetric :
    (imaginaryPart M : Matrix n n ℂ).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (selfAdjoint.mem_iff.mp (imaginaryPart M).2)

/-- Joint eigenspaces of the real and imaginary parts of a normal matrix; for `M` normal these are
commuting symmetric operators. -/
private noncomputable def jointEig (i : ℂ × ℂ) : Submodule ℂ (EuclideanSpace ℂ n) :=
  eigenspace (realPart M : Matrix n n ℂ).toEuclideanLin i.2
    ⊓ eigenspace (imaginaryPart M : Matrix n n ℂ).toEuclideanLin i.1

private theorem jointEig_isInternal [IsStarNormal M] : DirectSum.IsInternal (jointEig M) :=
  LinearMap.IsSymmetric.directSum_isInternal_of_commute
    (realPart_toEuclideanLin_isSymmetric M) (imaginaryPart_toEuclideanLin_isSymmetric M)
    (by
      have hc := (isStarNormal_iff_commute_realPart_imaginaryPart.mp ‹IsStarNormal M›).eq
      change (realPart M : Matrix n n ℂ).toEuclideanLin
          * (imaginaryPart M : Matrix n n ℂ).toEuclideanLin
          = (imaginaryPart M : Matrix n n ℂ).toEuclideanLin
          * (realPart M : Matrix n n ℂ).toEuclideanLin
      refine LinearMap.ext fun v => WithLp.ofLp_injective 2 ?_
      change (realPart M : Matrix n n ℂ) *ᵥ ((imaginaryPart M : Matrix n n ℂ) *ᵥ WithLp.ofLp v)
          = (imaginaryPart M : Matrix n n ℂ) *ᵥ ((realPart M : Matrix n n ℂ) *ᵥ WithLp.ofLp v)
      rw [mulVec_mulVec, mulVec_mulVec, hc])

set_option maxHeartbeats 600000 in
-- The bump covers the irreducible `whnf` of `subordinateOrthonormalBasis` (the same API
-- `Matrix.IsHermitian.eigenvectorBasis` is built on). It is near-minimal (500000 does not suffice)
-- and isolated in this auxiliary def, so none of the public results below need a bump.
/-- An orthonormal eigenbasis of a normal matrix, its (complex) eigenvalues, and the eigen
equation, bundled together so the public API projects out consistent components. The real and
imaginary parts of `M` are commuting symmetric operators, so their joint eigenspaces give an
internal direct sum; a subordinate orthonormal basis diagonalizes both, hence `M`. The eigenvalue
is `(real-part eigenvalue) + i•(imaginary-part one)`. -/
private noncomputable def normalSpectralAux [IsStarNormal M] :
    Σ' (B : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)),
      {μ : n → ℂ // ∀ j, M *ᵥ ⇑(B j) = μ j • ⇑(B j)} := by
  classical
  have hAsym := realPart_toEuclideanLin_isSymmetric M
  have hBsym := imaginaryPart_toEuclideanLin_isSymmetric M
  have hOF : OrthogonalFamily ℂ (fun i => ↥(jointEig M i)) (fun i => (jointEig M i).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hAsym hBsym
  have hInt : DirectSum.IsInternal (jointEig M) := jointEig_isInternal M
  have hIndep : iSupIndep (jointEig M) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (jointEig M)).mp hInt |>.1
  have hFinSet : {i | jointEig M i ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hIndep
  haveI : Finite {i // jointEig M i ≠ ⊥} := hFinSet.to_subtype
  haveI : Fintype {i // jointEig M i ≠ ⊥} := Fintype.ofFinite _
  have hIntJ : DirectSum.IsInternal (fun i : {i // jointEig M i ≠ ⊥} => jointEig M i) :=
    DirectSum.isInternal_ne_bot_iff.mpr hInt
  have hOFJ : OrthogonalFamily ℂ (fun i : {i // jointEig M i ≠ ⊥} => ↥(jointEig M i))
      (fun i => (jointEig M i).subtypeₗᵢ) := hOF.comp Subtype.coe_injective
  set eFin := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) with heFin
  set B : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
    (hIntJ.subordinateOrthonormalBasis finrank_euclideanSpace hOFJ).reindex eFin with hB_def
  set idxJ : n → {i // jointEig M i ≠ ⊥} := fun j =>
    hIntJ.subordinateOrthonormalBasisIndex finrank_euclideanSpace (eFin.symm j) hOFJ with hidxJ
  set p : n → ℂ × ℂ := fun j => (idxJ j).val with hp
  set μ : n → ℂ := fun j => (p j).2 + Complex.I * (p j).1 with hμ_def
  have hmem : ∀ j, B j ∈ jointEig M (p j) := by
    intro j
    rw [hB_def, OrthonormalBasis.reindex_apply]
    exact hIntJ.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace (eFin.symm j) hOFJ
  have hre : ∀ j, (realPart M : Matrix n n ℂ) *ᵥ ⇑(B j) = (p j).2 • ⇑(B j) := by
    intro j
    have h := mem_eigenspace_iff.mp (hmem j).1
    simpa using congrArg (WithLp.ofLp) h
  have him : ∀ j, (imaginaryPart M : Matrix n n ℂ) *ᵥ ⇑(B j) = (p j).1 • ⇑(B j) := by
    intro j
    have h := mem_eigenspace_iff.mp (hmem j).2
    simpa using congrArg (WithLp.ofLp) h
  have hmul : ∀ j, M *ᵥ ⇑(B j) = μ j • ⇑(B j) := by
    intro j
    rw [← realPart_add_I_smul_imaginaryPart M, add_mulVec, smul_mulVec, hre, him, hμ_def, smul_smul,
      add_smul]
  exact ⟨B, μ, hmul⟩

/-- A choice of an orthonormal basis of eigenvectors of a normal matrix. -/
noncomputable def normalEigenvectorBasis [IsStarNormal M] :
    OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
  (normalSpectralAux M).1

/-- The (complex) eigenvalues of a normal matrix, indexed compatibly with
`normalEigenvectorBasis`. -/
noncomputable def normalEigenvalues [IsStarNormal M] : n → ℂ :=
  (normalSpectralAux M).2.1

/-- The defining eigen equation: `M *ᵥ B j = μ j • B j`. Mirrors
`Matrix.IsHermitian.mulVec_eigenvectorBasis`. -/
lemma mulVec_normalEigenvectorBasis [IsStarNormal M] (j : n) :
    M *ᵥ ⇑(normalEigenvectorBasis M j) = normalEigenvalues M j • ⇑(normalEigenvectorBasis M j) :=
  (normalSpectralAux M).2.2 j

/-- Unitary matrix whose columns are `Matrix.normalEigenvectorBasis`. Mirrors
`Matrix.IsHermitian.eigenvectorUnitary`. -/
noncomputable def normalEigenvectorUnitary [IsStarNormal M] : Matrix.unitaryGroup n ℂ :=
  ⟨(EuclideanSpace.basisFun n ℂ).toBasis.toMatrix (normalEigenvectorBasis M).toBasis,
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary (normalEigenvectorBasis M)⟩

/-- `mulVec` of the change-of-basis matrix of an orthonormal basis on a standard basis vector
returns the corresponding basis vector. -/
private lemma basisFun_toMatrix_mulVec_single
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (j : n) :
    (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b.toBasis *ᵥ Pi.single j 1 = ⇑(b j) := by
  rw [mulVec_single_one]; rfl

/-- `normalEigenvectorUnitary` applied to a standard basis vector returns the eigenvector. -/
theorem normalEigenvectorUnitary_mulVec [IsStarNormal M] (j : n) :
    (normalEigenvectorUnitary M : Matrix n n ℂ) *ᵥ Pi.single j 1
      = ⇑(normalEigenvectorBasis M j) := by
  unfold normalEigenvectorUnitary
  exact basisFun_toMatrix_mulVec_single (normalEigenvectorBasis M) j

/-- The columns of `normalEigenvectorUnitary` are the eigenvector basis. -/
@[simp]
theorem normalEigenvectorUnitary_apply [IsStarNormal M] (i j : n) :
    normalEigenvectorUnitary M i j = ⇑(normalEigenvectorBasis M j) i := by
  unfold normalEigenvectorUnitary
  rfl

/-- **Spectral theorem for normal matrices** (bundled form). A normal complex matrix `M` is
diagonalized by its eigenvector unitary: `M = U * diagonal μ * Uᴴ`. -/
theorem spectral_theorem_of_isStarNormal [IsStarNormal M] :
    M = (normalEigenvectorUnitary M : Matrix n n ℂ) * Matrix.diagonal (normalEigenvalues M)
        * star (normalEigenvectorUnitary M : Matrix n n ℂ) := by
  set B := normalEigenvectorBasis M with hBdef
  set μ := normalEigenvalues M with hμdef
  set V : Matrix n n ℂ := (normalEigenvectorUnitary M : Matrix n n ℂ) with hVdef
  have hmul : ∀ j, M *ᵥ ⇑(B j) = μ j • ⇑(B j) := mulVec_normalEigenvectorBasis M
  have hVmem : V ∈ Matrix.unitaryGroup n ℂ := (normalEigenvectorUnitary M).2
  have hcol : ∀ j, V *ᵥ Pi.single j 1 = ⇑(B j) := fun j => normalEigenvectorUnitary_mulVec M j
  have key : M * V = V * Matrix.diagonal μ := by
    refine Matrix.ext fun i k => ?_
    have hUVcol : (M * V) *ᵥ Pi.single k 1 = μ k • ⇑(B k) := by rw [← mulVec_mulVec, hcol, hmul]
    rw [mulVec_single_one] at hUVcol
    have lhs : (M * V) i k = μ k * (B k) i := by have := congrFun hUVcol i; simpa using this
    rw [lhs, Matrix.mul_diagonal]
    exact mul_comm (μ k) ((B k) i)
  have hVstar : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hVmem
  calc M = M * (V * star V) := by rw [hVstar, mul_one]
    _ = (M * V) * star V := by rw [mul_assoc]
    _ = (V * Matrix.diagonal μ) * star V := by rw [key]

/-- **Spectral theorem for normal matrices** (existential form). A normal complex matrix `M`
(`Mᴴ * M = M * Mᴴ`) is unitarily diagonalizable. Specific to `ℂ`: a real normal matrix need not be
orthogonally diagonalizable over `ℝ`. -/
theorem exists_isUnitary_conj_diagonal_of_isStarNormal (hM : IsStarNormal M) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (μ : n → ℂ),
      M = (U : Matrix n n ℂ) * Matrix.diagonal μ * star (U : Matrix n n ℂ) := by
  haveI := hM
  exact ⟨normalEigenvectorUnitary M, normalEigenvalues M, spectral_theorem_of_isStarNormal M⟩

/-- Converse direction: a unitarily-diagonalizable matrix is normal. -/
theorem isStarNormal_of_isUnitary_conj_diagonal (U : Matrix.unitaryGroup n ℂ) (μ : n → ℂ)
    (hM : M = (U : Matrix n n ℂ) * Matrix.diagonal μ * star (U : Matrix n n ℂ)) :
    IsStarNormal M := by
  set U' : Matrix n n ℂ := (U : Matrix n n ℂ) with hU'
  set D : Matrix n n ℂ := Matrix.diagonal μ with hD
  have hUU' : star U' * U' = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hstarM : star M = U' * star D * star U' := by
    rw [hM, star_mul, star_mul, star_star, mul_assoc]
  have hDcomm : D * star D = star D * D := by
    rw [hD, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact mul_comm _ _
  have hMsM : M * star M = U' * (D * star D) * star U' := by
    rw [hstarM, hM]
    calc U' * D * star U' * (U' * star D * star U')
        = U' * D * (star U' * U') * star D * star U' := by noncomm_ring
      _ = U' * (D * star D) * star U' := by rw [hUU']; noncomm_ring
  have hsMM : star M * M = U' * (star D * D) * star U' := by
    rw [hstarM, hM]
    calc U' * star D * star U' * (U' * D * star U')
        = U' * star D * (star U' * U') * D * star U' := by noncomm_ring
      _ = U' * (star D * D) * star U' := by rw [hUU']; noncomm_ring
  refine ⟨?_⟩
  change star M * M = M * star M
  rw [hsMM, hMsM, hDcomm]

/-- **Spectral theorem for normal matrices** (iff form). A complex matrix is normal iff it is
unitarily diagonalizable. -/
theorem isStarNormal_iff_exists_isUnitary_conj_diagonal :
    IsStarNormal M ↔ ∃ (U : Matrix.unitaryGroup n ℂ) (μ : n → ℂ),
      M = (U : Matrix n n ℂ) * Matrix.diagonal μ * star (U : Matrix n n ℂ) :=
  ⟨exists_isUnitary_conj_diagonal_of_isStarNormal M,
    fun ⟨U, μ, hM⟩ => isStarNormal_of_isUnitary_conj_diagonal M U μ hM⟩

/-! ### Consequences: determinant, trace, characteristic polynomial, rank

All follow from `spectral_theorem_of_isStarNormal` (`M = U * diagonal μ * Uᴴ`) and the invariance
of these quantities under conjugation by the unitary `U`. They mirror the Hermitian-case results in
`Mathlib/Analysis/Matrix/Spectrum.lean`. -/

/-- The determinant of a normal matrix is the product of its eigenvalues. -/
theorem det_eq_prod_normalEigenvalues [IsStarNormal M] :
    M.det = ∏ i, normalEigenvalues M i := by
  have hUU : (normalEigenvectorUnitary M : Matrix n n ℂ)
      * star (normalEigenvectorUnitary M : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (normalEigenvectorUnitary M).2
  conv_lhs => rw [spectral_theorem_of_isStarNormal M]
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hUU, Matrix.det_one,
    one_mul, Matrix.det_diagonal]

/-- The trace of a normal matrix is the sum of its eigenvalues. -/
theorem trace_eq_sum_normalEigenvalues [IsStarNormal M] :
    M.trace = ∑ i, normalEigenvalues M i := by
  have hUU' : star (normalEigenvectorUnitary M : Matrix n n ℂ)
      * (normalEigenvectorUnitary M : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (normalEigenvectorUnitary M).2
  conv_lhs => rw [spectral_theorem_of_isStarNormal M]
  rw [Matrix.trace_mul_comm, ← mul_assoc, hUU', one_mul, Matrix.trace_diagonal]

/-- The characteristic polynomial of a normal matrix splits as `∏ (X - μ i)` over `ℂ`. -/
theorem charpoly_eq_prod_normalEigenvalues [IsStarNormal M] :
    M.charpoly = ∏ i, (Polynomial.X - Polynomial.C (normalEigenvalues M i)) := by
  have hUU' : star (normalEigenvectorUnitary M : Matrix n n ℂ)
      * (normalEigenvectorUnitary M : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (normalEigenvectorUnitary M).2
  conv_lhs => rw [spectral_theorem_of_isStarNormal M]
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, hUU', one_mul, Matrix.charpoly_diagonal]

/-- The spectrum of a normal matrix is the range of its eigenvalues. -/
theorem spectrum_eq_range_normalEigenvalues [IsStarNormal M] :
    spectrum ℂ M = Set.range (normalEigenvalues M) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_eq_prod_normalEigenvalues]
  simp only [Polynomial.isRoot_prod, Finset.mem_univ, true_and, Polynomial.root_X_sub_C,
    Set.mem_range]

/-- The rank of a normal matrix is the number of nonzero eigenvalues. -/
theorem rank_eq_card_normalEigenvalues_ne_zero [IsStarNormal M] :
    M.rank = Fintype.card {i // normalEigenvalues M i ≠ 0} := by
  have hUU : (normalEigenvectorUnitary M : Matrix n n ℂ)
      * star (normalEigenvectorUnitary M : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (normalEigenvectorUnitary M).2
  have hUU' : star (normalEigenvectorUnitary M : Matrix n n ℂ)
      * (normalEigenvectorUnitary M : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (normalEigenvectorUnitary M).2
  have hdetU : IsUnit (normalEigenvectorUnitary M : Matrix n n ℂ).det :=
    Matrix.isUnit_det_of_right_inverse hUU
  have hdetsU : IsUnit (star (normalEigenvectorUnitary M : Matrix n n ℂ)).det :=
    Matrix.isUnit_det_of_right_inverse hUU'
  conv_lhs => rw [spectral_theorem_of_isStarNormal M]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetsU,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdetU, Matrix.rank_diagonal]

end Matrix
