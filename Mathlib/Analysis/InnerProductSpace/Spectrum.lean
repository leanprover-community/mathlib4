/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Tactic.SimpRw

#align_import analysis.inner_product_space.spectrum from "leanprover-community/mathlib"@"6b0169218d01f2837d79ea2784882009a0da1aa1"

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

These are forms of the *diagonalization theorem* for self-adjoint operators on finite-dimensional
inner product spaces.

## TODO

Spectral theory for compact self-adjoint operators, bounded self-adjoint operators.

## Tags

self-adjoint operator, spectral theorem, diagonalization theorem

-/


variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

open scoped ComplexConjugate

open Module.End

namespace LinearMap

namespace IsSymmetric

variable {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
theorem invariant_orthogonalComplement_eigenspace (μ : 𝕜) (v : E) (hv : v ∈ (eigenspace T μ)ᗮ) :
    T v ∈ (eigenspace T μ)ᗮ := by
  intro w hw
  have : T w = (μ : 𝕜) • w := by rwa [mem_eigenspace_iff] at hw
  simp [← hT w, this, inner_smul_left, hv w hw]
#align linear_map.is_symmetric.invariant_orthogonal_eigenspace LinearMap.IsSymmetric.invariant_orthogonalComplement_eigenspace

/-- The eigenvalues of a self-adjoint operator are real. -/
theorem conj_eigenvalue_eq_self {μ : 𝕜} (hμ : HasEigenvalue T μ) : conj μ = μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv₁
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v
#align linear_map.is_symmetric.conj_eigenvalue_eq_self LinearMap.IsSymmetric.conj_eigenvalue_eq_self

/-- The eigenspaces of a self-adjoint operator are mutually orthogonal. -/
theorem orthogonalFamily_eigenspaces :
    OrthogonalFamily 𝕜 (fun μ => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  by_cases hv' : v = 0
  · simp [hv']
  have H := hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hv, hv'⟩)
  rw [mem_eigenspace_iff] at hv hw
  refine Or.resolve_left ?_ hμν.symm
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).symm
#align linear_map.is_symmetric.orthogonal_family_eigenspaces LinearMap.IsSymmetric.orthogonalFamily_eigenspaces

theorem orthogonalFamily_eigenspaces' :
    OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => eigenspace T μ) fun μ =>
      (eigenspace T μ).subtypeₗᵢ :=
  hT.orthogonalFamily_eigenspaces.comp Subtype.coe_injective
#align linear_map.is_symmetric.orthogonal_family_eigenspaces' LinearMap.IsSymmetric.orthogonalFamily_eigenspaces'

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space is an invariant subspace of the operator. -/
theorem orthogonalComplement_iSup_eigenspaces_invariant ⦃v : E⦄ (hv : v ∈ (⨆ μ, eigenspace T μ)ᗮ) :
    T v ∈ (⨆ μ, eigenspace T μ)ᗮ := by
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  exact T.iInf_invariant hT.invariant_orthogonalComplement_eigenspace v hv
#align linear_map.is_symmetric.orthogonal_supr_eigenspaces_invariant LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_invariant

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space has no eigenvalues. -/
theorem orthogonalComplement_iSup_eigenspaces (μ : 𝕜) :
    eigenspace (T.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant) μ = ⊥ := by
  set p : Submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ
  refine eigenspace_restrict_eq_bot hT.orthogonalComplement_iSup_eigenspaces_invariant ?_
  have H₂ : eigenspace T μ ⟂ p := (Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)
  exact H₂.disjoint
#align linear_map.is_symmetric.orthogonal_supr_eigenspaces LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces

/-! ### Finite-dimensional theory -/


variable [FiniteDimensional 𝕜 E]

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot : (⨆ μ, eigenspace T μ)ᗮ = ⊥ := by
  have hT' : IsSymmetric _ :=
    hT.restrict_invariant hT.orthogonalComplement_iSup_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  haveI :=
    hT'.subsingleton_of_no_eigenvalue_finiteDimensional hT.orthogonalComplement_iSup_eigenspaces
  exact Submodule.eq_bot_of_subsingleton
#align linear_map.is_symmetric.orthogonal_supr_eigenspaces_eq_bot LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot

theorem orthogonalComplement_iSup_eigenspaces_eq_bot' :
    (⨆ μ : Eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
  show (⨆ μ : { μ // eigenspace T μ ≠ ⊥ }, eigenspace T μ)ᗮ = ⊥ by
    rw [iSup_ne_bot_subtype, hT.orthogonalComplement_iSup_eigenspaces_eq_bot]
#align linear_map.is_symmetric.orthogonal_supr_eigenspaces_eq_bot' LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot'

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` gives
an internal direct sum decomposition of `E`.

Note this takes `hT` as a `Fact` to allow it to be an instance. -/
noncomputable instance directSumDecomposition [hT : Fact T.IsSymmetric] :
    DirectSum.Decomposition fun μ : Eigenvalues T => eigenspace T μ :=
  haveI h : ∀ μ : Eigenvalues T, CompleteSpace (eigenspace T μ) := fun μ => by infer_instance
  hT.out.orthogonalFamily_eigenspaces'.decomposition
    (Submodule.orthogonal_eq_bot_iff.mp hT.out.orthogonalComplement_iSup_eigenspaces_eq_bot')
#align linear_map.is_symmetric.direct_sum_decomposition LinearMap.IsSymmetric.directSumDecomposition

theorem directSum_decompose_apply [_hT : Fact T.IsSymmetric] (x : E) (μ : Eigenvalues T) :
    DirectSum.decompose (fun μ : Eigenvalues T => eigenspace T μ) x μ =
      orthogonalProjection (eigenspace T μ) x :=
  rfl
#align linear_map.is_symmetric.direct_sum_decompose_apply LinearMap.IsSymmetric.directSum_decompose_apply

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` gives
an internal direct sum decomposition of `E`. -/
theorem direct_sum_isInternal : DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ :=
  hT.orthogonalFamily_eigenspaces'.isInternal_iff.mpr
    hT.orthogonalComplement_iSup_eigenspaces_eq_bot'
#align linear_map.is_symmetric.direct_sum_is_internal LinearMap.IsSymmetric.direct_sum_isInternal

section Version1

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization : E ≃ₗᵢ[𝕜] PiLp 2 fun μ : Eigenvalues T => eigenspace T μ :=
  hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily hT.orthogonalFamily_eigenspaces'
#align linear_map.is_symmetric.diagonalization LinearMap.IsSymmetric.diagonalization

@[simp]
theorem diagonalization_symm_apply (w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ) :
    hT.diagonalization.symm w = ∑ μ, w μ :=
  hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily_symm_apply
    hT.orthogonalFamily_eigenspaces' w
#align linear_map.is_symmetric.diagonalization_symm_apply LinearMap.IsSymmetric.diagonalization_symm_apply

/-- *Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
theorem diagonalization_apply_self_apply (v : E) (μ : Eigenvalues T) :
    hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ := by
  suffices
    ∀ w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm fun μ => (μ : 𝕜) • w μ by
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using
      congr_arg (fun w => hT.diagonalization w μ) (this (hT.diagonalization v))
  intro w
  have hwT : ∀ μ, T (w μ) = (μ : 𝕜) • w μ := fun μ => mem_eigenspace_iff.1 (w μ).2
  simp only [hwT, diagonalization_symm_apply, map_sum, Submodule.coe_smul_of_tower]
#align linear_map.is_symmetric.diagonalization_apply_self_apply LinearMap.IsSymmetric.diagonalization_apply_self_apply

end Version1

section Version2

variable {n : ℕ} (hn : FiniteDimensional.finrank 𝕜 E = n)

/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.

TODO Postcompose with a permutation so that these eigenvectors are listed in increasing order of
eigenvalue. -/
noncomputable irreducible_def eigenvectorBasis : OrthonormalBasis (Fin n) 𝕜 E :=
  hT.direct_sum_isInternal.subordinateOrthonormalBasis hn hT.orthogonalFamily_eigenspaces'
#align linear_map.is_symmetric.eigenvector_basis LinearMap.IsSymmetric.eigenvectorBasis

/-- The sequence of real eigenvalues associated to the standard orthonormal basis of eigenvectors
for a self-adjoint operator `T` on `E`.

TODO Postcompose with a permutation so that these eigenvalues are listed in increasing order. -/
noncomputable irreducible_def eigenvalues (i : Fin n) : ℝ :=
  @RCLike.re 𝕜 _ <| (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces').val
#align linear_map.is_symmetric.eigenvalues LinearMap.IsSymmetric.eigenvalues

theorem hasEigenvector_eigenvectorBasis (i : Fin n) :
    HasEigenvector T (hT.eigenvalues hn i) (hT.eigenvectorBasis hn i) := by
  let v : E := hT.eigenvectorBasis hn i
  let μ : 𝕜 :=
    (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces').val
  simp_rw [eigenvalues]
  change HasEigenvector T (RCLike.re μ) v
  have key : HasEigenvector T μ v := by
    have H₁ : v ∈ eigenspace T μ := by
      simp_rw [v, eigenvectorBasis]
      exact
        hT.direct_sum_isInternal.subordinateOrthonormalBasis_subordinate hn i
          hT.orthogonalFamily_eigenspaces'
    have H₂ : v ≠ 0 := by simpa using (hT.eigenvectorBasis hn).toBasis.ne_zero i
    exact ⟨H₁, H₂⟩
  have re_μ : ↑(RCLike.re μ) = μ := by
    rw [← RCLike.conj_eq_iff_re]
    exact hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector key)
  simpa [re_μ] using key
#align linear_map.is_symmetric.has_eigenvector_eigenvector_basis LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis

theorem hasEigenvalue_eigenvalues (i : Fin n) : HasEigenvalue T (hT.eigenvalues hn i) :=
  Module.End.hasEigenvalue_of_hasEigenvector (hT.hasEigenvector_eigenvectorBasis hn i)
#align linear_map.is_symmetric.has_eigenvalue_eigenvalues LinearMap.IsSymmetric.hasEigenvalue_eigenvalues

@[simp]
theorem apply_eigenvectorBasis (i : Fin n) :
    T (hT.eigenvectorBasis hn i) = (hT.eigenvalues hn i : 𝕜) • hT.eigenvectorBasis hn i :=
  mem_eigenspace_iff.mp (hT.hasEigenvector_eigenvectorBasis hn i).1
#align linear_map.is_symmetric.apply_eigenvector_basis LinearMap.IsSymmetric.apply_eigenvectorBasis

/-- *Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
theorem eigenvectorBasis_apply_self_apply (v : E) (i : Fin n) :
    (hT.eigenvectorBasis hn).repr (T v) i =
      hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr v i := by
  suffices
    ∀ w : EuclideanSpace 𝕜 (Fin n),
      T ((hT.eigenvectorBasis hn).repr.symm w) =
        (hT.eigenvectorBasis hn).repr.symm fun i => hT.eigenvalues hn i * w i by
    simpa [OrthonormalBasis.sum_repr_symm] using
      congr_arg (fun v => (hT.eigenvectorBasis hn).repr v i)
        (this ((hT.eigenvectorBasis hn).repr v))
  intro w
  simp_rw [← OrthonormalBasis.sum_repr_symm, map_sum, map_smul, apply_eigenvectorBasis]
  apply Fintype.sum_congr
  intro a
  rw [smul_smul, mul_comm]
#align linear_map.is_symmetric.diagonalization_basis_apply_self_apply LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply

end Version2

section Simultaneous

section Pair

variable {A B : E →ₗ[𝕜] E}  {α β : 𝕜} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A)

theorem eigenspace_invariant  (α : 𝕜) : ∀ v ∈ (eigenspace A α), (B v ∈ eigenspace A α) := by
  intro v hv
  rw [eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply, ← comp_apply A B v, hAB,
  comp_apply B A v, ← map_smul, ← map_sub, hv, map_zero] at *

theorem invariant_subspace_inf_eigenspace_eq_restrict {F : Submodule 𝕜 E} (S : E →ₗ[𝕜] E)
    (μ : 𝕜) (hInv : ∀ v ∈ F, S v ∈ F) : (eigenspace S μ) ⊓ F =
    Submodule.map (Submodule.subtype F)
    (eigenspace (S.restrict (hInv)) μ) := by
  ext v
  constructor
  · intro h
    simp only [Submodule.mem_map, Submodule.coeSubtype, Subtype.exists, exists_and_right,
      exists_eq_right, mem_eigenspace_iff]; use h.2
    exact Eq.symm (SetCoe.ext (_root_.id (Eq.symm (mem_eigenspace_iff.mp h.1))))
  · intro h
    simp only [Submodule.mem_inf]
    constructor
    · simp only [Submodule.mem_map, Submodule.coeSubtype, Subtype.exists, exists_and_right,
      exists_eq_right, mem_eigenspace_iff, SetLike.mk_smul_mk, restrict_apply,
      Subtype.mk.injEq] at h
      obtain ⟨_, hy⟩ := h
      simpa [mem_eigenspace_iff]
    · simp only [Submodule.coeSubtype] at h
      obtain ⟨y, hy⟩ := h
      simp only [← hy.2, Submodule.coeSubtype, SetLike.coe_mem]

theorem invariant_subspace_inf_eigenspace_eq_restrict' : (fun (γ : 𝕜) ↦
    Submodule.map (Submodule.subtype (eigenspace A α)) (eigenspace (B.restrict
    (eigenspace_invariant hAB α)) γ)) = (fun (γ : 𝕜) ↦ (eigenspace B γ ⊓ eigenspace A α)) := by
  funext γ
  exact Eq.symm (invariant_subspace_inf_eigenspace_eq_restrict B γ (eigenspace_invariant hAB α))

theorem iSup_restrict_eq_top: (⨆ γ , (eigenspace (LinearMap.restrict B
    (eigenspace_invariant hAB α)) γ)) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    exact orthogonalComplement_iSup_eigenspaces_eq_bot (LinearMap.IsSymmetric.restrict_invariant hB
    (eigenspace_invariant hAB α))

theorem iSup_simultaneous_eigenspaces_eq_top :
    (⨆ (α : 𝕜), (⨆ (γ : 𝕜), (eigenspace B γ ⊓ eigenspace A α))) = ⊤ := by
  have : (fun (α : 𝕜) ↦  eigenspace A α)  = fun (α : 𝕜) ↦
      (⨆ (γ : 𝕜), (eigenspace B γ ⊓ eigenspace A α)) := by
    funext; rw [← invariant_subspace_inf_eigenspace_eq_restrict' hAB,
       ← Submodule.map_iSup, iSup_restrict_eq_top hB hAB, Submodule.map_top,
       Submodule.range_subtype]
  rw [← Submodule.orthogonal_eq_bot_iff.mp (hA.orthogonalComplement_iSup_eigenspaces_eq_bot), this]

theorem orthogonality_of_simultaneous_eigenspaces_of_pairwise_commuting_symmetric :
    OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace B i.1 ⊓ eigenspace A i.2 : Submodule 𝕜 E))
    (fun i => (eigenspace B i.1 ⊓ eigenspace A i.2).subtypeₗᵢ) := by
  refine orthogonalFamily_iff_pairwise.mpr ?_
  intro i j hij v ⟨hv1 , hv2⟩
  have H:=  (Iff.not (Iff.symm Prod.ext_iff)).mpr hij
  push_neg at H
  by_cases C: i.1 = j.1
  <;> intro w ⟨hw1, hw2⟩
  · exact orthogonalFamily_iff_pairwise.mp hA.orthogonalFamily_eigenspaces (H C) hv2 w hw2
  · exact orthogonalFamily_iff_pairwise.mp hB.orthogonalFamily_eigenspaces C hv1 w hw1

theorem DirectSum.IsInternal_of_simultaneous_eigenspaces_of_pairwise_commuting_symmetric:
    DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) ↦ (eigenspace B i.1 ⊓ eigenspace A i.2)):= by
  apply (OrthogonalFamily.isInternal_iff
    (orthogonality_of_simultaneous_eigenspaces_of_pairwise_commuting_symmetric hA hB)).mpr
  rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
  exact iSup_simultaneous_eigenspaces_eq_top hA hB hAB

end Pair

section Tuple

universe u

variable {n m : Type u} [Fintype n] [Fintype m] (T : n → (E →ₗ[𝕜] E))
    (hT :(∀ (i : n), ((T i).IsSymmetric)))
    (hC : (∀ (i j : n), (T i) ∘ₗ (T j) = (T j) ∘ₗ (T i)))

open Classical

theorem invariance_iInf [Nonempty n] (i : n) :
    ∀ γ : {x // x ≠ i} → 𝕜, ∀ v ∈ (⨅ (j : {x // x ≠ i}),
    eigenspace ((Subtype.restrict (fun x ↦ x ≠ i) T) j) (γ j)), (T i) v ∈ (⨅ (j : {x // x ≠ i}),
    eigenspace ((Subtype.restrict (fun x ↦ x ≠ i) T) j) (γ j)) := by
  intro γ v hv
  simp only [Submodule.mem_iInf] at *
  exact fun i_1 ↦ eigenspace_invariant (hC (↑i_1) i) (γ i_1) v (hv i_1)

theorem iSup_iInf_fun_index_split_single {α β γ : Type*} [DecidableEq α] [CompleteLattice γ]
    (i : α) (s : α → β → γ) : (⨆ f : α → β, ⨅ x, s x (f x)) =
      ⨆ f' : {y // y ≠ i} → β, ⨆ y : β, s i y ⊓ ⨅ x' : {y // y ≠ i}, (s x' (f' x')) := by
  rw [← (Equiv.funSplitAt i β).symm.iSup_comp, iSup_prod, iSup_comm]
  congr!  with f' y
  rw [iInf_split_single _ i, iInf_subtype]
  congr! with x hx
  · simp
  · simp [dif_neg hx]

theorem invariant_subspace_eigenspace_exhaust {F : Submodule 𝕜 E} (S : E →ₗ[𝕜] E)
    (hS: IsSymmetric S) (hInv : ∀ v ∈ F, S v ∈ F) : ⨆ μ, Submodule.map F.subtype
    (eigenspace (S.restrict hInv) μ)  = F := by
 conv_lhs => rw [← Submodule.map_iSup]
 conv_rhs => rw [← Submodule.map_subtype_top F]
 congr!
 have H : IsSymmetric (S.restrict hInv) := fun x y ↦ hS (F.subtype x) ↑y
 apply Submodule.orthogonal_eq_bot_iff.mp (H.orthogonalComplement_iSup_eigenspaces_eq_bot)

theorem orthogonalComplement_iSup_iInf_eigenspaces_eq_bot:
    (⨆ (γ : n → 𝕜), (⨅ (j : n), (eigenspace (T j) (γ j)) : Submodule 𝕜 E))ᗮ = ⊥ := by
  revert T
  refine' Fintype.induction_subsingleton_or_nontrivial n _ _
  · intro m _ hhm T hT _
    simp only [Submodule.orthogonal_eq_bot_iff]
    by_cases case : Nonempty m
    · have i := choice case
      have := uniqueOfSubsingleton i
      conv => lhs; rhs; ext γ; rw [ciInf_subsingleton i]
      rw [← (Equiv.funUnique m 𝕜).symm.iSup_comp]
      apply Submodule.orthogonal_eq_bot_iff.mp ((hT i).orthogonalComplement_iSup_eigenspaces_eq_bot)
    · simp only [not_nonempty_iff] at case
      simp only [iInf_of_empty, ciSup_unique]
  · intro m hm hmm H T hT hC
    obtain ⟨w, i , h⟩ := exists_pair_ne m
    simp only [ne_eq] at h
    have D := H {x // x ≠ i} (Fintype.card_subtype_lt (p := fun (x : m) ↦ ¬x = i) (x := i)
      (by simp only [not_true_eq_false, not_false_eq_true])) (Subtype.restrict (fun x ↦ x ≠ i) T)
        (fun (i_1 : {x // x ≠ i}) ↦ hT ↑i_1) (fun (i_1 j : { x // x ≠ i }) ↦ hC ↑i_1 ↑j)
    simp only [Submodule.orthogonal_eq_bot_iff] at *
    have E : (⨆ (γ : {x // x ≠ i} → 𝕜), (⨆ μ : 𝕜, (eigenspace (T i) μ ⊓ (⨅ (j : {x // x ≠ i}),
    eigenspace (Subtype.restrict (fun x ↦ x ≠ i) T j) (γ j))))) = ⨆ (γ : {x // x ≠ i} → 𝕜),
    (⨅ (j : {x // x ≠ i}), eigenspace (Subtype.restrict (fun x ↦ x ≠ i) T j) (γ j)) := by
      conv => lhs; rhs; ext γ; rhs; ext μ; rw [invariant_subspace_inf_eigenspace_eq_restrict (T i) μ
        (invariance_iInf T hC i γ)]
      conv => lhs; rhs; ext γ; rw [invariant_subspace_eigenspace_exhaust (T i) (hT i)
        (invariance_iInf T hC i γ)]
    rw [← E] at D
    rw [iSup_iInf_fun_index_split_single i (fun _ ↦ (fun μ ↦ (eigenspace (T _) μ )))]
    exact D

theorem orthogonalFamily_iInf_eigenspaces : OrthogonalFamily 𝕜 (fun (γ : n → 𝕜) =>
    (⨅ (j : n), (eigenspace (T j) (γ j)) : Submodule 𝕜 E))
    (fun (γ : n → 𝕜) => (⨅ (j : n), (eigenspace (T j) (γ j))).subtypeₗᵢ) := by
  intro f g hfg Ef Eg
  obtain ⟨a , ha⟩ := Function.ne_iff.mp hfg
  have H := (orthogonalFamily_eigenspaces (hT a) ha)
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coeSubtype, Subtype.forall] at H
  apply H
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (f _)).mp Ef.2 _
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (g _)).mp Eg.2 _

/-- The Hilbert space on which a finite commuting family of symmetric linear operators acts
decomposes as an internal direct sum of simultaneous eigenspaces for these operators. -/
theorem direct_sum_isInternal_simultaneous : DirectSum.IsInternal (fun (α : n → 𝕜) ↦
    ⨅ (j : n), (eigenspace (T j) (α j))) := by
    rw [OrthogonalFamily.isInternal_iff]
    · exact orthogonalComplement_iSup_iInf_eigenspaces_eq_bot T hT hC
    · exact orthogonalFamily_iInf_eigenspaces T hT

end Tuple

end Simultaneous

end IsSymmetric

end LinearMap
section Nonneg

@[simp]
theorem inner_product_apply_eigenvector {μ : 𝕜} {v : E} {T : E →ₗ[𝕜] E}
    (h : v ∈ Module.End.eigenspace T μ) : ⟪v, T v⟫ = μ * (‖v‖ : 𝕜) ^ 2 := by
  simp only [mem_eigenspace_iff.mp h, inner_smul_right, inner_self_eq_norm_sq_to_K]
#align inner_product_apply_eigenvector inner_product_apply_eigenvector

theorem eigenvalue_nonneg_of_nonneg {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x : E, 0 ≤ RCLike.re ⟪x, T x⟫) : 0 ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv.2
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 := by
    have := congr_arg RCLike.re (inner_product_apply_eigenvector hv.1)
    -- Porting note: why can't `exact_mod_cast` do this? These lemmas are marked `norm_cast`
    rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul] at this
    exact mod_cast this
  exact (mul_nonneg_iff_of_pos_right hpos).mp (this ▸ hnn v)
#align eigenvalue_nonneg_of_nonneg eigenvalue_nonneg_of_nonneg

theorem eigenvalue_pos_of_pos {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x : E, 0 < RCLike.re ⟪x, T x⟫) : 0 < μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv.2
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 := by
    have := congr_arg RCLike.re (inner_product_apply_eigenvector hv.1)
    -- Porting note: why can't `exact_mod_cast` do this? These lemmas are marked `norm_cast`
    rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul] at this
    exact mod_cast this
  exact (mul_pos_iff_of_pos_right hpos).mp (this ▸ hnn v)
#align eigenvalue_pos_of_pos eigenvalue_pos_of_pos


end Nonneg
