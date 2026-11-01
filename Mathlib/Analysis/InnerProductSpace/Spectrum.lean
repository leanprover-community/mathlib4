/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-! # Spectral theory of self-adjoint operators

This file covers the spectral theory of self-adjoint operators on an inner product space.

The first part of the file covers general properties, true without any condition on boundedness or
compactness of the operator or finite-dimensionality of the underlying space, notably:
* `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`: the eigenvalues are real
* `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`: the eigenspaces are orthogonal
* `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces`: the restriction of the operator to
  the mutual orthogonal complement of the eigenspaces has, itself, no eigenvectors

The second part of the file covers properties of self-adjoint operators in finite dimension.
Letting `T` be a self-adjoint operator on a finite-dimensional inner product space `T`,
* The definition `LinearMap.IsSymmetric.diagonalization` provides a linear isometry equivalence `E`
  to the direct sum of the eigenspaces of `T`.  The theorem
  `LinearMap.IsSymmetric.diagonalization_apply_self_apply` states that, when `T` is transferred via
  this equivalence to an operator on the direct sum, it acts diagonally.
* The definition `LinearMap.IsSymmetric.eigenvectorBasis` provides an orthonormal basis for `E`
  consisting of eigenvectors of `T`, with `LinearMap.IsSymmetric.eigenvalues` giving the
  corresponding list of eigenvalues, as real numbers.  The definition
  `LinearMap.IsSymmetric.eigenvectorBasis` gives the associated linear isometry equivalence
  from `E` to Euclidean space, and the theorem
  `LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply` states that, when `T` is
  transferred via this equivalence to an operator on Euclidean space, it acts diagonally.
* `LinearMap.IsSymmetric.eigenvalues` gives the eigenvalues in decreasing order.  This is
  done for several reasons: (i) This agrees with the standard convention of listing singular
  values in decreasing order, with the operator norm as the first singular value
  (ii) For positive compact operators on an infinite-dimensional space, one can list the nonzero
  eigenvalues in decreasing (but not increasing) order since they converge to zero. (iii) This
  simplifies several theorem statements. For example the Schur-Horn theorem states that the diagonal
  of the matrix representation of a selfadjoint linear map is majorized by the eigenvalue sequence
  listed in decreasing order.

These are forms of the *diagonalization theorem* for self-adjoint operators on finite-dimensional
inner product spaces.

The third part of the file covers properties of compact self-adjoint operators:
* `orthogonalComplement_iSup_eigenspaces_eq_bot`: the eigenspaces of a compact self-adjoint operator
  have trivial orthogonal complement.
* `finite_dimensional_eigenspace`: the eigenspaces of a compact self-adjoint operator are
  finite-dimensional.

## TODO

Spectral theory for bounded self-adjoint operators.

## Tags

self-adjoint operator, spectral theorem, diagonalization theorem

-/

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped ComplexConjugate

open Module End WithLp

namespace LinearMap

namespace IsSymmetric

variable {T : E →ₗ[𝕜] E}

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
theorem invariant_orthogonalComplement_eigenspace (hT : T.IsSymmetric) (μ : 𝕜)
    (v : E) (hv : v ∈ (eigenspace T μ)ᗮ) : T v ∈ (eigenspace T μ)ᗮ := by
  intro w hw
  have : T w = (μ : 𝕜) • w := by rwa [mem_eigenspace_iff] at hw
  simp [← hT w, this, inner_smul_left, hv w hw]

/-- The eigenvalues of a self-adjoint operator are real. -/
theorem conj_eigenvalue_eq_self (hT : T.IsSymmetric) {μ : 𝕜} (hμ : HasEigenvalue T μ) :
    conj μ = μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv₁
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v

/-- The eigenspaces of a self-adjoint operator are mutually orthogonal. -/
theorem orthogonalFamily_eigenspaces (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  by_cases hv' : v = 0
  · simp [hv']
  have H := hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hv, hv'⟩)
  rw [mem_eigenspace_iff] at hv hw
  refine Or.resolve_left ?_ hμν.symm
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).symm

theorem orthogonalFamily_eigenspaces' (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => eigenspace T μ) fun μ =>
      (eigenspace T μ).subtypeₗᵢ :=
  hT.orthogonalFamily_eigenspaces.comp Subtype.coe_injective

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space is an invariant subspace of the operator. -/
theorem orthogonalComplement_iSup_eigenspaces_invariant (hT : T.IsSymmetric)
    ⦃v : E⦄ (hv : v ∈ (⨆ μ, eigenspace T μ)ᗮ) : T v ∈ (⨆ μ, eigenspace T μ)ᗮ := by
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  exact T.iInf_invariant hT.invariant_orthogonalComplement_eigenspace v hv

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space has no eigenvalues. -/
theorem orthogonalComplement_iSup_eigenspaces (hT : T.IsSymmetric) (μ : 𝕜) :
    eigenspace (T.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant) μ = ⊥ := by
  set p : Submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ
  refine eigenspace_restrict_eq_bot hT.orthogonalComplement_iSup_eigenspaces_invariant ?_
  have H₂ : eigenspace T μ ⟂ p := (Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)
  exact H₂.disjoint

/-! ### Finite-dimensional theory -/

variable [FiniteDimensional 𝕜 E]

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot (hT : T.IsSymmetric) :
    (⨆ μ, eigenspace T μ)ᗮ = ⊥ := by
  have hT' : IsSymmetric _ :=
    hT.restrict_invariant hT.orthogonalComplement_iSup_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  have :=
    hT'.subsingleton_of_no_eigenvalue_finiteDimensional hT.orthogonalComplement_iSup_eigenspaces
  exact Submodule.eq_bot_of_subsingleton

theorem orthogonalComplement_iSup_eigenspaces_eq_bot' (hT : T.IsSymmetric) :
    (⨆ μ : Eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
  show (⨆ μ : { μ // eigenspace T μ ≠ ⊥ }, eigenspace T μ)ᗮ = ⊥ by
    rw [iSup_ne_bot_subtype, hT.orthogonalComplement_iSup_eigenspaces_eq_bot]

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` gives
an internal direct sum decomposition of `E`.

Note this takes `hT` as a `Fact` to allow it to be an instance. -/
noncomputable instance directSumDecomposition [hT : Fact T.IsSymmetric] :
    DirectSum.Decomposition fun μ : Eigenvalues T => eigenspace T μ :=
  haveI h : ∀ μ : Eigenvalues T, CompleteSpace (eigenspace T μ) := fun μ => by infer_instance
  hT.out.orthogonalFamily_eigenspaces'.decomposition
    (Submodule.orthogonal_eq_bot_iff.mp hT.out.orthogonalComplement_iSup_eigenspaces_eq_bot')

theorem directSum_decompose_apply [_hT : Fact T.IsSymmetric] (x : E) (μ : Eigenvalues T) :
    DirectSum.decompose (fun μ : Eigenvalues T => eigenspace T μ) x μ =
      (eigenspace T μ).orthogonalProjectionOnto x :=
  rfl

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` gives
an internal direct sum decomposition of `E`. -/
theorem direct_sum_isInternal (hT : T.IsSymmetric) :
    DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ :=
  hT.orthogonalFamily_eigenspaces'.isInternal_iff.mpr
    hT.orthogonalComplement_iSup_eigenspaces_eq_bot'

section Version1

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization (hT : T.IsSymmetric) : E ≃ₗᵢ[𝕜] PiLp 2 fun μ :
    Eigenvalues T => eigenspace T μ :=
  hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily hT.orthogonalFamily_eigenspaces'

@[simp]
theorem diagonalization_symm_apply (hT : T.IsSymmetric)
    (w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ) :
    hT.diagonalization.symm w = ∑ μ, w μ :=
  hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily_symm_apply
    hT.orthogonalFamily_eigenspaces' w

/-- *Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
theorem diagonalization_apply_self_apply (hT : T.IsSymmetric) (v : E) (μ : Eigenvalues T) :
    hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ := by
  suffices
    ∀ w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm (toLp 2 fun μ => (μ : 𝕜) • w μ) by
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using
      congr(hT.diagonalization $(this (hT.diagonalization v)) μ)
  intro w
  have hwT : ∀ μ, T (w μ) = (μ : 𝕜) • w μ := fun μ => mem_eigenspace_iff.1 (w μ).2
  simp only [diagonalization_symm_apply, map_sum, hwT, SetLike.val_smul]

end Version1

section Version2

variable {n : ℕ}

/-- Unsorted eigenvalues and eigenvectors.  These private definitions should not be used directly.
Instead use the functions eigenvalues and eigenvectorBasis defined below. -/
private noncomputable def unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : ℝ :=
  @RCLike.re 𝕜 _ (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces').val

private theorem hasEigenvalue_unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : HasEigenvalue T (hT.unsortedEigenvalues hn i) := by
  unfold unsortedEigenvalues
  let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces'
  rwa [Eigenvalues.val_mk, RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hx)]

private theorem exists_unsortedEigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {μ : 𝕜} (hμ : HasEigenvalue T μ) : ∃ i : Fin n, hT.unsortedEigenvalues hn i = μ := by
  let (eq := hx) x : Eigenvalues T := ⟨μ, hμ⟩
  obtain ⟨i, hi⟩ := hT.direct_sum_isInternal.exists_subordinateOrthonormalBasisIndex_eq hn
    hT.orthogonalFamily_eigenspaces' (hasEigenvalue_iff.mp x.prop)
  use i
  rw [unsortedEigenvalues, hi, hx, Eigenvalues.val_mk, ← RCLike.conj_eq_iff_re,
    hT.conj_eigenvalue_eq_self hμ]

private theorem card_filter_unsortedEigenvalues_eq (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) :
    Finset.card {i | hT.unsortedEigenvalues hn i = μ} = Module.finrank 𝕜 (eigenspace T μ) := by
  by_cases hμ : HasEigenvalue T μ
  · convert!
      hT.direct_sum_isInternal.card_filter_subordinateOrthonormalBasisIndex_eq hn
        hT.orthogonalFamily_eigenspaces' ⟨μ, hμ⟩ with i
    unfold unsortedEigenvalues
    let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces'
    rw [Eigenvalues.val_mk, RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hx)]
    exact Subtype.mk_eq_mk.symm
  · rw [Module.End.hasEigenvalue_iff.not_left.mp hμ, finrank_bot, Finset.card_filter_eq_zero_iff]
    intro i _ rfl
    exact hμ (hT.hasEigenvalue_unsortedEigenvalues hn i)

private noncomputable def unsortedEigenvectorBasis (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) : OrthonormalBasis (Fin n) 𝕜 E :=
  hT.direct_sum_isInternal.subordinateOrthonormalBasis hn hT.orthogonalFamily_eigenspaces'

private theorem hasEigenvector_eigenvectorBasis_helper (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    HasEigenvector T (hT.unsortedEigenvalues hn i) (hT.unsortedEigenvectorBasis hn i) := by
  let v : E := hT.unsortedEigenvectorBasis hn i
  let μ : 𝕜 :=
    (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces').val
  simp_rw [unsortedEigenvalues]
  change HasEigenvector T (RCLike.re μ) v
  have key : HasEigenvector T μ v := by
    have H₁ : v ∈ eigenspace T μ := by
      simp_rw [v, unsortedEigenvectorBasis]
      exact
        hT.direct_sum_isInternal.subordinateOrthonormalBasis_subordinate hn i
          hT.orthogonalFamily_eigenspaces'
    have H₂ : v ≠ 0 := by simpa using (hT.unsortedEigenvectorBasis hn).toBasis.ne_zero i
    exact ⟨H₁, H₂⟩
  have re_μ : ↑(RCLike.re μ) = μ := by
    rw [← RCLike.conj_eq_iff_re]
    exact hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector key)
  simpa [re_μ] using key

/-- The eigenvalues for a self-adjoint operator `T` on a
finite-dimensional inner product space `E`, sorted in decreasing order -/
@[no_expose]
noncomputable def eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Fin n → ℝ :=
  (hT.unsortedEigenvalues hn) ∘ Tuple.sortDesc (hT.unsortedEigenvalues hn)

theorem exists_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {μ : 𝕜}
    (hμ : HasEigenvalue T μ) : ∃ i : Fin n, hT.eigenvalues hn i = μ := by
  obtain ⟨i, hi⟩ := hT.exists_unsortedEigenvalues_eq hn hμ
  use (Tuple.sortDesc (hT.unsortedEigenvalues hn)).symm i
  simp [eigenvalues, hi]

theorem card_filter_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) :
    Finset.card {i | hT.eigenvalues hn i = μ} = Module.finrank 𝕜 (eigenspace T μ) := by
  rw [← hT.card_filter_unsortedEigenvalues_eq hn, eigenvalues]
  apply Finset.card_equiv (Tuple.sortDesc (hT.unsortedEigenvalues hn))
  simp

/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.  Eigenvectors are sorted in decreasing
order of their eigenvalues. -/
@[no_expose]
noncomputable def eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  (hT.direct_sum_isInternal.subordinateOrthonormalBasis
    hn hT.orthogonalFamily_eigenspaces').reindex
      (Tuple.sortDesc (hT.unsortedEigenvalues hn)).symm

theorem hasEigenvector_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : HasEigenvector T (hT.eigenvalues hn i) (hT.eigenvectorBasis hn i) := by
  rw [eigenvalues, eigenvectorBasis, OrthonormalBasis.reindex_apply]
  apply hasEigenvector_eigenvectorBasis_helper

/-- Eigenvalues are sorted in decreasing order. -/
theorem eigenvalues_antitone (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Antitone (hT.eigenvalues hn) := by
  rw [eigenvalues]
  exact Tuple.antitone_sortDesc _

theorem hasEigenvalue_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    HasEigenvalue T (hT.eigenvalues hn i) :=
  Module.End.hasEigenvalue_of_hasEigenvector (hT.hasEigenvector_eigenvectorBasis hn i)

@[simp]
theorem apply_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T (hT.eigenvectorBasis hn i) = (hT.eigenvalues hn i : 𝕜) • hT.eigenvectorBasis hn i :=
  mem_eigenspace_iff.mp (hT.hasEigenvector_eigenvectorBasis hn i).1

/-- *Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
theorem eigenvectorBasis_apply_self_apply (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (v : E) (i : Fin n) :
    (hT.eigenvectorBasis hn).repr (T v) i =
      hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr v i := by
  suffices
    ∀ w : EuclideanSpace 𝕜 (Fin n),
      T ((hT.eigenvectorBasis hn).repr.symm w) =
        (hT.eigenvectorBasis hn).repr.symm (toLp 2 fun i ↦ hT.eigenvalues hn i * w i) by
    simpa [OrthonormalBasis.sum_repr_symm] using
      congr((hT.eigenvectorBasis hn).repr $(this ((hT.eigenvectorBasis hn).repr v)) i)
  intro w
  simp_rw [← OrthonormalBasis.sum_repr_symm, map_sum, map_smul, apply_eigenvectorBasis]
  apply Fintype.sum_congr
  intro a
  rw [smul_smul, mul_comm, ofLp_toLp]

theorem toMatrix_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    letI b := (hT.eigenvectorBasis hn).toBasis
    T.toMatrix b b = Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn) := by
  ext i j
  simp [toMatrix_apply, Matrix.diagonal_apply, RCLike.real_smul_eq_coe_mul]
  grind

open Polynomial in
theorem charpoly_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.charpoly = ∏ i, (X - C (hT.eigenvalues hn i : 𝕜)) := by
  simp [← T.charpoly_toMatrix (hT.eigenvectorBasis hn).toBasis, toMatrix_eigenvectorBasis,
    Matrix.charpoly_diagonal]

theorem roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hT.eigenvalues hn) Finset.univ.val := by
  rw [← charpoly_toMatrix _ (hT.eigenvectorBasis hn).toBasis, toMatrix_eigenvectorBasis,
    Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp

theorem sort_roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    (T.charpoly.roots.map RCLike.re).sort (· ≥ ·) = List.ofFn (hT.eigenvalues hn) := by
  simp_rw [hT.roots_charpoly_eq_eigenvalues, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  have := hn.symm
  convert List.mergeSort_of_pairwise ?_
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  convert (hT.eigenvalues_antitone hn).sortedGE_ofFn

theorem eigenvalues_eq_eigenvalues_iff {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    [FiniteDimensional 𝕜 E'] {T' : E' →ₗ[𝕜] E'} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (hT' : T'.IsSymmetric) (hn' : Module.finrank 𝕜 E' = n) :
    hT.eigenvalues hn = hT'.eigenvalues hn' ↔ T.charpoly = T'.charpoly where
  mp h := by rw [hT.charpoly_eq hn, hT'.charpoly_eq hn', h]
  mpr h := by
    rw [← List.ofFn_inj, ← sort_roots_charpoly_eq_eigenvalues, ← sort_roots_charpoly_eq_eigenvalues,
      h]

theorem splits_charpoly (hT : T.IsSymmetric) : T.charpoly.Splits := by
  refine Polynomial.splits_iff_card_roots.mpr ?_
  simp [hT.roots_charpoly_eq_eigenvalues rfl, LinearMap.charpoly_natDegree]

theorem det_eq_prod_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.det = ∏ i, (hT.eigenvalues hn i : 𝕜) := by
  simp [det_eq_prod_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.prod_ofFn]

end Version2

end IsSymmetric

end LinearMap

section Nonneg

-- Cannot be @[simp] because the LHS is not in simp normal form
theorem inner_product_apply_eigenvector {μ : 𝕜} {v : E} {T : E →ₗ[𝕜] E}
    (h : T v = μ • v) : ⟪v, T v⟫ = μ * (‖v‖ : 𝕜) ^ 2 := by
  simp only [h, inner_smul_right, inner_self_eq_norm_sq_to_K]

theorem eigenvalue_nonneg_of_nonneg {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x, 0 ≤ RCLike.re ⟪x, T x⟫) : 0 ≤ μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : 0 < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector hv₁)
  exact (mul_nonneg_iff_of_pos_right hpos).mp (this ▸ hnn v)

theorem eigenvalue_pos_of_pos {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x, x ≠ 0 → 0 < RCLike.re ⟪x, T x⟫) : 0 < μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : 0 < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector hv₁)
  exact (mul_pos_iff_of_pos_right hpos).mp (this ▸ hnn v hv₂)

end Nonneg

namespace ContinuousLinearMap

section Version1

variable [CompleteSpace E] {T : E →L[𝕜] E}

theorem eq_zero_of_forall_hasEigenvalue_eq_zero (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (∀ μ, HasEigenvalue (T : End 𝕜 E) μ → μ = 0) ↔ T = 0 := by
  rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero, ← T.spectralRadius_eq_nnnorm hT'.isSelfAdjoint,
    spectralRadius_eq_of_unital, ← not_iff_not, ENNReal.iSup_eq_zero]
  push Not
  apply exists_congr
  simp +contextual [hT.hasEigenvalue_iff_mem_spectrum]

/-- The **Spectral Theorem** for compact self-adjoint operators: the eigenspaces of a compact
self-adjoint operator have trivial orthogonal complement. -/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot
    (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ := by
  let S : (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ →L[𝕜] (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ :=
    T.restrict hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_compact : IsCompactOperator S :=
    hT.restrict' hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.IsSymmetric :=
    hT'.restrict_invariant (hT'.orthogonalComplement_iSup_eigenspaces_invariant)
  have hS μ : eigenspace (S : Module.End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ) μ = ⊥ :=
    hT'.orthogonalComplement_iSup_eigenspaces _
  have h μ : HasEigenvalue (S : End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ) μ → μ = 0 := by
    simp_all [hasEigenvalue_iff]
  rw [eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm] at h
  rw [← Submodule.subsingleton_iff_eq_bot]
  by_contra! hV
  simpa [h] using hS 0

/-- The **Spectral Theorem** for compact self-adjoint operators: the eigenspaces of a compact
self-adjoint operator are finite-dimensional. -/
theorem finite_dimensional_eigenspace (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ) := by
  replace hT := hT.restrict'
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp (eigenspace_mem_invtSubmodule T.toLinearMap μ))
  rw [restrict_eigenspace, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

end Version1

section Version2

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {T : E →L[𝕜] E}

/-- Index for the chosen Hilbert basis of each eigenspace. -/
private noncomputable def eigenspaceBasisIndex (T : E →L[𝕜] E) (ν : 𝕜) :
    Set (eigenspace (T : End 𝕜 E) ν) :=
  (exists_hilbertBasis 𝕜 (eigenspace (T : End 𝕜 E) ν)).choose

/-- Chosen Hilbert basis of each eigenspace. -/
private noncomputable def eigenspaceBasis (T : E →L[𝕜] E) (ν : 𝕜) :
    HilbertBasis (eigenspaceBasisIndex T ν) 𝕜 (eigenspace (T : End 𝕜 E) ν) :=
  (exists_hilbertBasis 𝕜 (eigenspace (T : End 𝕜 E) ν)).choose_spec.choose

/-- Index type for unsorted family of eigenspaceBasis. -/
private def UnsortedIndex (T : E →L[𝕜] E) := Σ ν : 𝕜, eigenspaceBasisIndex T ν

/-- The unsorted eigenvalues, indexed by `UnsortedIndex`. -/
private noncomputable def unsortedEigenvalues (T : E →L[𝕜] E) (i : UnsortedIndex T) : ℝ :=
  RCLike.re i.1

private theorem hasEigenvalue_fst (T : E →L[𝕜] E) (i : UnsortedIndex T) :
    HasEigenvalue (T : End 𝕜 E) i.1 := by
  rw [hasEigenvalue_iff]
  intro h
  have : Subsingleton (eigenspace (T : End 𝕜 E) i.1) := Submodule.subsingleton_iff_eq_bot.mpr h
  exact (T.eigenspaceBasis i.1).orthonormal.ne_zero i.2 (Subsingleton.elim _ _)

private theorem ofReal_unsortedEigenvalues (T : E →L[𝕜] E) (hT' : T.IsSymmetric)
    (i : UnsortedIndex T) : ((T.unsortedEigenvalues i : ℝ) : 𝕜) = i.1 := by
  have h := hT'.conj_eigenvalue_eq_self (hasEigenvalue_fst T i)
  unfold unsortedEigenvalues
  exact RCLike.conj_eq_iff_re.mp h

private theorem hasEigenvalue_unsortedEigenvalues (T : E →L[𝕜] E) (hT' : T.IsSymmetric)
    (i : UnsortedIndex T) :
    HasEigenvalue (T : End 𝕜 E) (T.unsortedEigenvalues i) := by
  rw [ofReal_unsortedEigenvalues T hT' i]
  exact hasEigenvalue_fst T i

/-- A HilbertBasis of `E` based on the unsorted eigenvalues. -/
private noncomputable def unsortedEigenvectorBasis (hT : IsCompactOperator T)
    (hT' : T.IsSymmetric) : HilbertBasis (UnsortedIndex T) 𝕜 E := HilbertBasis.mkOfOrthogonalEqBot
  (hT'.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun v ↦ (T.eigenspaceBasis v).orthonormal))
  (by
    rw [← Submodule.orthogonal_closure, eq_bot_iff,
      ← orthogonalComplement_iSup_eigenspaces_eq_bot hT hT']
    refine Submodule.orthogonal_le (iSup_le fun ν x hx ↦ ?_)
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (((T.eigenspaceBasis ν).hasSum_repr ⟨x, hx⟩).mapL (eigenspace (T : End 𝕜 E) ν).subtypeL)
      (Filter.Eventually.of_forall fun s ↦ Submodule.sum_mem _ fun i _ ↦ ?_)
    exact Submodule.le_topologicalClosure _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨ν, i⟩, rfl⟩)))

private theorem hasEigenvector_unsortedEigenvectorBasis (hT : IsCompactOperator T)
    (hT' : T.IsSymmetric) (i : UnsortedIndex T) :
    HasEigenvector (T : End 𝕜 E) (unsortedEigenvalues T i)
      (unsortedEigenvectorBasis hT hT' i) := by
  unfold unsortedEigenvectorBasis
  erw [HilbertBasis.coe_mkOfOrthogonalEqBot, ofReal_unsortedEigenvalues T hT' i]
  refine ⟨(T.eigenspaceBasis i.1 i.2).2, ?_⟩
  intro h
  exact (T.eigenspaceBasis i.1).orthonormal.ne_zero i.2 (Subtype.ext h)

private theorem tendsto_unsortedEigenvalues (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    Filter.Tendsto (unsortedEigenvalues T) Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hfin
  set b := unsortedEigenvectorBasis hT hT'
  simp at hfin
  -- compactness: cover the relatively compact image of the unit ball by `ε/2`-balls
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp
    (hT.isCompact_closure_image_closedBall 1).totallyBounded (ε / 2) (half_pos hε)
  have hmem : ∀ i, ∃ c ∈ t, dist (T (b i)) c < ε / 2 := by
    intro i
    have h1 : T (b i) ∈ closure (T '' Metric.closedBall (0 : E) 1) :=
      subset_closure ⟨b i, by simp [b.orthonormal.1 i], rfl⟩
    have h2 := hcover h1
    simp only [Set.mem_iUnion, Metric.mem_ball] at h2
    obtain ⟨c, hc, hd⟩ := h2
    exact ⟨c, hc, hd⟩
  choose c hct hcd using hmem
  -- pigeonhole: two distinct large eigenvalue indices share a center
  obtain ⟨x, hx, y, hy, hxy, hc⟩ :=
    hfin.exists_ne_map_eq_of_mapsTo (f := c) (fun i _ => hct i) htfin
  -- Hence, their images are less than `ε` apart
  have hlt : dist (T (b x)) (T (b y)) < ε := by
    calc dist (T (b x)) (T (b y))
        ≤ dist (T (b x)) (c x) + dist (c x) (T (b y)) := dist_triangle _ _ _
      _ = dist (T (b x)) (c x) + dist (T (b y)) (c y) := by rw [hc, dist_comm (c y)]
      _ < ε / 2 + ε / 2 := add_lt_add (hcd x) (hcd y)
      _ = ε := by ring
  -- but their images are also at least `ε` apart
  have hdist : ε ≤ dist (T (b x)) (T (b y)) := by
    have hb : ∀ i, T (b i) = ((unsortedEigenvalues T i : ℝ) : 𝕜) • b i := fun i =>
      (hasEigenvector_unsortedEigenvectorBasis hT hT' i).apply_eq_smul
    rw [dist_eq_norm, hb, hb, sub_eq_add_neg, ← neg_smul]
    refine (sq_le_sq₀ hε.le (norm_nonneg _)).1 ?_
    simp_rw [sq]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) _ _
      (by simp [inner_smul_left, inner_smul_right, b.orthonormal.2 hxy])]
    simp only [norm_smul, b.orthonormal.1, RCLike.norm_ofReal, mul_one]
    nlinarith [pow_le_pow_left₀ hε.le hx 2, sq_nonneg |unsortedEigenvalues T y|]
  exact absurd hdist (not_le.mpr hlt)

/-- Index type for the nonzero (unsorted) eigenvalues. -/
private abbrev NonzeroIndex (T : E →L[𝕜] E) :=
  {i : UnsortedIndex T // unsortedEigenvalues T i ≠ 0}

/-- Index type for the zero eigenvalues. -/
private abbrev ZeroIndex (T : E →L[𝕜] E) :=
  {i : UnsortedIndex T // ¬ unsortedEigenvalues T i ≠ 0}

/-- Sort lexicographically such that `i < j` ↔ `|μ i| < |μ j|` when
  `|μ i| ≠ |μ j|`, `μ i < μ j` when `μ i ≠ μ j` and arbitrary otherwise. -/
private noncomputable def NonzeroIndex.key (i : NonzeroIndex T) :
    ℝᵒᵈ ×ₗ ℝᵒᵈ ×ₗ Cardinal.{max u v} :=
  toLex (OrderDual.toDual |unsortedEigenvalues T i.1|,
    toLex (OrderDual.toDual (unsortedEigenvalues T i.1), embeddingToCardinal i.1))

private theorem NonzeroIndex.key_injective :
    Function.Injective (NonzeroIndex.key (T := T)) := by
  intro i j h
  simp only [NonzeroIndex.key, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
  exact Subtype.ext (embeddingToCardinal.injective h.2.2)

private noncomputable instance : LinearOrder (NonzeroIndex T) :=
  LinearOrder.lift' NonzeroIndex.key NonzeroIndex.key_injective

private theorem finite_Iio (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (i : NonzeroIndex T) : (Set.Iio i).Finite := by
  have hε : 0 < |unsortedEigenvalues T i.1| := abs_pos.mpr i.2
  have hF := Filter.eventually_cofinite.mp
    (Metric.tendsto_nhds.mp (tendsto_unsortedEigenvalues hT hT') _ hε)
  refine (hF.preimage Subtype.val_injective.injOn).subset fun j hj => ?_
  have h' : NonzeroIndex.key j < NonzeroIndex.key i := hj
  unfold NonzeroIndex.key at h'
  rw [Prod.Lex.lt_iff] at h'
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs, not_lt]
  rcases h' with h' | ⟨h', -⟩
  · exact h'.le
  · exact (OrderDual.toDual_inj.mp h').ge

/-- Since there are only finitely many eigenvalues larger than any given eigenvalue, we can assign
  it a rank based on that. -/
private noncomputable def rank (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (i : NonzeroIndex T) : ℕ :=
  (finite_Iio hT hT' i).toFinset.card

private theorem rank_strictMono (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    StrictMono (rank hT hT') := by
  intro i j hij
  unfold rank
  apply Finset.card_lt_card
  rw [Set.Finite.toFinset_ssubset_toFinset]
  exact ⟨Set.Iio_subset_Iio hij.le, fun hsub => lt_irrefl i (hsub hij)⟩

/-- For a HilbertBasis `b` indexed by `ι`, `b.reindex (e : ι ≃ ι')` is a HilbertBasis indexed
  by `ι'` -/
noncomputable def _root_.HilbertBasis.reindex {ι ι' : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    HilbertBasis ι' 𝕜 E :=
  HilbertBasis.mk (v := fun i' => b (e.symm i'))
    (b.orthonormal.comp _ e.symm.injective)
    (by
      have h : Set.range (fun i' => b (e.symm i')) = Set.range b := e.symm.surjective.range_comp b
      rw [h]
      exact b.dense_span.ge)

/-- Index type for the nonzero (sorted) eigenvalues. -/
@[no_expose]
def SortedIndex (hT : IsCompactOperator T) (hT' : T.IsSymmetric) : Type := Set.range (rank hT hT')

/-- Equivalence between the index types of the sorted and unsorted eigenvalues. -/
private noncomputable def sortEquiv (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    NonzeroIndex T ≃ SortedIndex hT hT' :=
  Equiv.ofInjective (rank hT hT') (rank_strictMono hT hT').injective

/-- Index type for the eigenvalues. -/
@[no_expose]
def eigenIndex (hT : IsCompactOperator T) (hT' : T.IsSymmetric) := SortedIndex hT hT' ⊕ ZeroIndex T

private noncomputable def eigenEquiv (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (eigenIndex hT hT') ≃ UnsortedIndex T :=
  (Equiv.sumCongr (sortEquiv hT hT') (Equiv.refl (ZeroIndex T))).symm.trans
    (Equiv.sumCompl fun i : UnsortedIndex T => unsortedEigenvalues T i ≠ 0)

/-- The eigenvalues for a compact self-adjoint operator `T`. -/
@[no_expose]
noncomputable def eigenvalues (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (eigenIndex hT hT') → ℝ :=
  T.unsortedEigenvalues ∘ (eigenEquiv hT hT')

/-- A HilbertBasis based on the eigendecomposition for a compact self-adjoint operator `T`. -/
@[no_expose]
noncomputable def eigenvectorBasis (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    HilbertBasis (eigenIndex hT hT') 𝕜 E :=
  (unsortedEigenvectorBasis hT hT').reindex (eigenEquiv hT hT').symm

private theorem coe_eigenvectorBasis (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (i : eigenIndex hT hT') :
    eigenvectorBasis hT hT' i = unsortedEigenvectorBasis hT hT' (eigenEquiv hT hT' i) := by
  unfold eigenvectorBasis HilbertBasis.reindex
  rw [HilbertBasis.coe_mk]
  simp

theorem hasEigenvector_eigenvectorBasis (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (i : eigenIndex hT hT') :
    HasEigenvector (T : End 𝕜 E) (eigenvalues hT hT' i) (eigenvectorBasis hT hT' i) := by
  rw [coe_eigenvectorBasis]
  unfold eigenvalues
  exact hasEigenvector_unsortedEigenvectorBasis hT hT' (eigenEquiv hT hT' i)

theorem apply_eigenvectorBasis (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (i : eigenIndex hT hT') :
    T (eigenvectorBasis hT hT' i) = (eigenvalues hT hT' i : 𝕜) • eigenvectorBasis hT hT' i :=
  (hasEigenvector_eigenvectorBasis hT hT' i).apply_eq_smul

theorem tendsto_eigenvalues (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    Filter.Tendsto (eigenvalues hT hT') Filter.cofinite (nhds 0) := by
  unfold eigenvalues
  exact (tendsto_unsortedEigenvalues hT hT').comp
    (eigenEquiv hT hT').toEmbedding.injective.tendsto_cofinite

open InnerProductSpace in
theorem hasSum_eigenvectorBasis (hT : IsCompactOperator T) (hT' : T.IsSymmetric) (x : E) :
    HasSum (fun i => (eigenvalues hT hT' i : 𝕜) •
      rankOne 𝕜 (eigenvectorBasis hT hT' i) (eigenvectorBasis hT hT' i) x) (T x) := by
  have h := ((eigenvectorBasis hT hT').hasSum_repr x).mapL T
  convert h using 1
  ext i
  simp [apply_eigenvectorBasis, smul_smul, HilbertBasis.repr_apply_apply, mul_comm]

/-- A compact self-adjoint operator `T : E →L[𝕜] E` has a Hilbert basis `b` consisting of
eigenvectors `b i` with eigenvalues `μ i`. -/
theorem exists_eigenvectorBasis
    (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    ∃ (ι : Type (max u v)) (b : HilbertBasis ι 𝕜 E) (μ : ι → 𝕜),
      ∀ i, T (b i) = (μ i : 𝕜) • b i := by
  set V : 𝕜 → Submodule 𝕜 E := fun ν ↦ eigenspace (T : End 𝕜 E) ν
  choose w bν _ using fun ν ↦ exists_hilbertBasis 𝕜 (V ν)
  let v : (Σ ν : 𝕜, w ν) → E := fun a ↦ (V a.1).subtypeₗᵢ (bν a.1 a.2)
  have hv : Orthonormal 𝕜 v :=
    hT'.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (v_family := fun ν ↦ bν ν) (fun ν ↦ (bν ν).orthonormal)
  have hsp : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    rw [← Submodule.orthogonal_closure, eq_bot_iff,
      ← orthogonalComplement_iSup_eigenspaces_eq_bot hT hT']
    refine Submodule.orthogonal_le (iSup_le fun ν x hx ↦ ?_)
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (((bν ν).hasSum_repr ⟨x, hx⟩).mapL (V ν).subtypeL)
      (Filter.Eventually.of_forall fun s ↦ Submodule.sum_mem _ fun i _ ↦ ?_)
    exact Submodule.le_topologicalClosure _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨ν, i⟩, rfl⟩))
  let b : HilbertBasis (Σ ν : 𝕜, w ν) 𝕜 E := HilbertBasis.mkOfOrthogonalEqBot hv hsp
  have hb : ⇑b = v := HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp
  refine ⟨_, b, fun a ↦ a.1, fun a ↦ ?_⟩
  simpa [hb, v] using mem_eigenspace_iff.mp (bν a.1 a.2).2

end Version2

end ContinuousLinearMap
