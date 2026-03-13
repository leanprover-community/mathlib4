/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Operator.FredholmAlternative
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Data.Fin.Tuple.Sort

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
  haveI :=
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
      (eigenspace T μ).orthogonalProjection x :=
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
      congr_arg (fun w => hT.diagonalization w μ) (this (hT.diagonalization v))
  intro w
  have hwT : ∀ μ, T (w μ) = (μ : 𝕜) • w μ := fun μ => mem_eigenspace_iff.1 (w μ).2
  simp only [diagonalization_symm_apply, map_sum, hwT, SetLike.val_smul]

end Version1

section Version2

variable {n : ℕ}

set_option backward.privateInPublic true in
/-- Unsorted eigenvalues and eigenvectors.  These private definitions should not be used directly.
Instead use the functions eigenvalues and eigenvectorBasis defined below. -/
private noncomputable def unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : ℝ :=
  @RCLike.re 𝕜 _ <| (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
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
  · convert hT.direct_sum_isInternal.card_filter_subordinateOrthonormalBasisIndex_eq hn
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

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The eigenvalues for a self-adjoint operator `T` on a
finite-dimensional inner product space `E`, sorted in decreasing order -/
noncomputable irreducible_def eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Fin n → ℝ :=
  (hT.unsortedEigenvalues hn) ∘ Tuple.sort (hT.unsortedEigenvalues hn) ∘ @Fin.revPerm n

theorem exists_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {μ : 𝕜}
    (hμ : HasEigenvalue T μ) : ∃ i : Fin n, hT.eigenvalues hn i = μ := by
  obtain ⟨i, hi⟩ := hT.exists_unsortedEigenvalues_eq hn hμ
  use ((Tuple.sort (hT.unsortedEigenvalues hn)).symm i).revPerm
  simp [eigenvalues_def, hi]

theorem card_filter_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) :
    Finset.card {i | hT.eigenvalues hn i = μ} = Module.finrank 𝕜 (eigenspace T μ) := by
  rw [← hT.card_filter_unsortedEigenvalues_eq hn, eigenvalues_def]
  apply Finset.card_equiv (Fin.revPerm.trans (Tuple.sort (hT.unsortedEigenvalues hn)))
  simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.  Eigenvectors are sorted in decreasing
order of their eigenvalues. -/
noncomputable irreducible_def eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  (hT.direct_sum_isInternal.subordinateOrthonormalBasis
    hn hT.orthogonalFamily_eigenspaces').reindex
      (Tuple.sort (hT.unsortedEigenvalues hn) * @Fin.revPerm n).symm

theorem hasEigenvector_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : HasEigenvector T (hT.eigenvalues hn i) (hT.eigenvectorBasis hn i) := by
  rw [eigenvalues_def, eigenvectorBasis_def, OrthonormalBasis.reindex_apply]
  apply hasEigenvector_eigenvectorBasis_helper

/-- Eigenvalues are sorted in decreasing order. -/
theorem eigenvalues_antitone (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Antitone (hT.eigenvalues hn) := by
  rw [eigenvalues_def, ← Function.comp_assoc]
  refine Monotone.comp_antitone ?_ ?_
  · apply Tuple.monotone_sort
  intro _ _ h
  exact Fin.rev_le_rev.mpr h

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
      congr_arg (fun v => (hT.eigenvectorBasis hn).repr v i)
        (this ((hT.eigenvectorBasis hn).repr v))
  intro w
  simp_rw [← OrthonormalBasis.sum_repr_symm, map_sum, map_smul, apply_eigenvectorBasis]
  apply Fintype.sum_congr
  intro a
  rw [smul_smul, mul_comm, ofLp_toLp]

end Version2

end IsSymmetric

end LinearMap

section Nonneg

-- Cannot be @[simp] because the LHS is not in simp normal form
theorem inner_product_apply_eigenvector {μ : 𝕜} {v : E} {T : E →ₗ[𝕜] E}
    (h : T v = μ • v) : ⟪v, T v⟫ = μ * (‖v‖ : 𝕜) ^ 2 := by
  simp only [h, inner_smul_right, inner_self_eq_norm_sq_to_K]

theorem eigenvalue_nonneg_of_nonneg {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x : E, 0 ≤ RCLike.re ⟪x, T x⟫) : 0 ≤ μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector hv₁)
  exact (mul_nonneg_iff_of_pos_right hpos).mp (this ▸ hnn v)

theorem eigenvalue_pos_of_pos {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x : E, 0 < RCLike.re ⟪x, T x⟫) : 0 < μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector hv₁)
  exact (mul_pos_iff_of_pos_right hpos).mp (this ▸ hnn v)

end Nonneg

namespace ContinuousLinearMap

variable [CompleteSpace E] {T : E →L[𝕜] E}

theorem eq_zero_of_forall_hasEigenvalue_eq_zero (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (∀ μ, HasEigenvalue (T : End 𝕜 E) μ → μ = 0) ↔ T = 0 := by
  constructor
  · intro h
    replace h : spectrum 𝕜 T ⊆ {0} := by
      intro μ hμ
      contrapose! h
      exact ⟨μ, (hT.hasEigenvalue_iff_mem_spectrum h).mpr hμ, h⟩
    rw [← isSelfAdjoint_iff_isSymmetric] at hT'
    rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero, ← T.spectralRadius_eq_nnnorm hT', spectralRadius]
    obtain (h | h) := Set.subset_singleton_iff_eq.mp h <;> simp [h]
  · rintro rfl μ h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    rw [hasEigenvector_iff, mem_genEigenspace_one] at hv
    exact (smul_eq_zero_iff_left hv.2).mp hv.1.symm


set_option backward.isDefEq.respectTransparency false in
/-- The **Spectral Theorem** for compact self-adjoint operators: the eigenspaces of a compact
self-adjoint operator have trivial orthogonal complement. -/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot
    (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ := by
  let S : (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ →L[𝕜] (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ :=
  { __ := T.restrict hT'.orthogonalComplement_iSup_eigenspaces_invariant
    cont := by fun_prop }
  have hS_compact : IsCompactOperator S :=
    hT.restrict' hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.IsSymmetric :=
    hT'.restrict_invariant (hT'.orthogonalComplement_iSup_eigenspaces_invariant)
  have hS μ : eigenspace (S : Module.End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ) μ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Subtype.ext_iff, Submodule.coe_zero, ← Submodule.mem_bot 𝕜,
      ← Submodule.inf_orthogonal_eq_bot (⨆ μ, eigenspace T μ : Submodule 𝕜 E)]
    refine ⟨Submodule.mem_iSup_of_mem μ ?_, v.2⟩
    rw [mem_eigenspace_iff] at hv ⊢
    exact Subtype.ext_iff.mp hv
  have h μ : HasEigenvalue (S : End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ) μ → μ = 0 := by
    intro hμ
    rw [hasEigenvalue_iff] at hμ
    specialize hS μ
    contradiction
  rw [eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm] at h
  rw [← Submodule.subsingleton_iff_eq_bot]
  by_contra! hV
  simpa [h] using hS 0

/-- The **Spectral Theorem** for compact self-adjoint operators: the eigenspaces of a compact
self-adjoint operator are finite-dimensional. -/
theorem finite_dimensional_eigenspace (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ) := by
  have inv : ∀ x ∈ eigenspace T.toLinearMap μ, T x ∈ eigenspace T.toLinearMap μ := by
    intro x hx
    rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hx ⊢
    rw [hx, map_smul, hx]
  replace hT := hT.restrict' inv
  have hx : T.restrict inv = μ • 1 := by
    ext x
    exact mem_eigenspace_iff.mp x.2
  rw [hx, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

end ContinuousLinearMap
