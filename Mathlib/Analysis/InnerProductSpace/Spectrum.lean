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

variable {A B : E →ₗ[𝕜] E}  {α β : 𝕜} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
     [FiniteDimensional 𝕜 E] (hAB : A ∘ₗ B = B ∘ₗ A)

theorem eigenspace_invariant  (α : 𝕜) : ∀ v ∈ (eigenspace A α), (B v ∈ eigenspace A α) := by
  intro v hv
  rw [eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply, ← comp_apply A B v, hAB,
  comp_apply B A v, ← map_smul, ← map_sub, hv, map_zero] at *

theorem iSup_restrict_eq_top: (⨆ γ , (eigenspace (LinearMap.restrict B
    (eigenspace_invariant hAB α)) γ)) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    exact orthogonalComplement_iSup_eigenspaces_eq_bot (LinearMap.IsSymmetric.restrict_invariant hB
    (eigenspace_invariant hAB α))

theorem eigen_extend (γ : 𝕜) (x : E) : x ∈ Submodule.map (Submodule.subtype (eigenspace A α))
    (eigenspace (B.restrict (eigenspace_invariant hAB α)) γ) → x ∈ eigenspace B γ := by
  simp only [mem_ker, sub_apply, Module.algebraMap_end_apply, Submodule.mem_map, mem_ker, sub_apply,
  Module.algebraMap_end_apply, Submodule.coeSubtype, Subtype.exists, SetLike.mk_smul_mk,
  exists_and_right, exists_eq_right] at *
  intro ⟨y, hy⟩
  exact (AddSubmonoid.mk_eq_zero (ker (A -
    (algebraMap 𝕜 (Module.End 𝕜 E)) α)).toAddSubgroup.toAddSubmonoid).mp hy

theorem restrict_eq_inf : (fun (γ : 𝕜) ↦
    Submodule.map (Submodule.subtype (eigenspace A α)) (eigenspace (B.restrict
    (eigenspace_invariant hAB α)) γ)) = (fun (γ : 𝕜) ↦ (eigenspace B γ ⊓ eigenspace A α)) := by
  funext γ
  ext x
  simp only [Submodule.mem_map, Submodule.coeSubtype, Subtype.exists, exists_and_right,
      exists_eq_right] at *
  constructor
  <;> intro ⟨x1, x2⟩
  · constructor
    <;> rw [SetLike.mem_coe]
    · apply eigen_extend hAB γ x
      simp only [Submodule.mem_map, Submodule.coeSubtype, Subtype.exists, exists_and_right,
        exists_eq_right]
      use x1
    · exact x1
  · use x2
    refine mem_eigenspace_iff.mpr ?h.a
    refine SetCoe.ext ?h.a.a
    rw [restrict_coe_apply]
    exact mem_eigenspace_iff.mp x1

theorem semi_final_exhaust : (⨆ (γ : 𝕜), (eigenspace B γ ⊓ eigenspace A α)) = eigenspace A α := by
   rw [← restrict_eq_inf hAB, ← Submodule.map_iSup, iSup_restrict_eq_top hB hAB,
   Submodule.map_top, Submodule.range_subtype]

theorem pre_exhaust :  (⨆ (γ : 𝕜), eigenspace A γ) =  ⊤ := by
  exact Submodule.orthogonal_eq_bot_iff.mp (hA.orthogonalComplement_iSup_eigenspaces_eq_bot)

theorem pre_exhaust': (fun (α : 𝕜) ↦  eigenspace A α)  = fun (α : 𝕜) ↦
    (⨆ (γ : 𝕜), (eigenspace B γ ⊓ eigenspace A α)) := by
  funext; exact (semi_final_exhaust hB hAB).symm

theorem exhaust : (⨆ (α : 𝕜), (⨆ (γ : 𝕜), (eigenspace B γ ⊓ eigenspace A α))) = ⊤ := by
  rw [← pre_exhaust hA, pre_exhaust' hB hAB]

theorem post_exhaust: (⨆ (α : 𝕜), (⨆ (γ : 𝕜), (eigenspace B γ ⊓ eigenspace A α)))ᗮ = ⊥ := by
  rw [Submodule.orthogonal_eq_bot_iff]
  apply exhaust hA hB hAB

theorem Orthogonality : OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) =>
    (eigenspace B i.1 ⊓ eigenspace A i.2 : Submodule 𝕜 E))
    (fun i => (eigenspace B i.1 ⊓ eigenspace A i.2).subtypeₗᵢ) := by
  apply orthogonalFamily_iff_pairwise.mpr ?_
  intro i j hij v hv
  have e:= (Iff.not (Iff.symm Prod.ext_iff)).mpr hij
  push_neg at e
  by_cases case : i.1 = j.1
  · have J := e case
    have Al := orthogonalFamily_iff_pairwise.mp hA.orthogonalFamily_eigenspaces J
    rw[@Submodule.mem_orthogonal']
    intro w hw
    simp only [Submodule.mem_inf] at hw
    have L := hv.2
    have M := hw.2
    exact inner_eq_zero_symm.mp (Al L w M)
  · push_neg at case
    rw[@Submodule.mem_orthogonal']
    intro w hw
    simp only [Submodule.mem_inf] at hw
    have L := hv.1
    have M := hw.1
    have Bl := orthogonalFamily_iff_pairwise.mp hB.orthogonalFamily_eigenspaces case
    exact inner_eq_zero_symm.mp (Bl L w M)

theorem post_post_exhaust: DirectSum.IsInternal
    (fun (i : 𝕜 × 𝕜) ↦ (eigenspace B i.1 ⊓ eigenspace A i.2)):= by
  have One := Orthogonality hA hB
  have Two : ⨆ (α : 𝕜), (⨆ (γ : 𝕜), (eigenspace B γ ⊓ eigenspace A α)) =
      ⨆ (i : 𝕜 × 𝕜), (eigenspace B i.1 ⊓ eigenspace A i.2) := by
    simp only [iSup_prod]
    exact iSup_comm
  have Three : ⨆ (i : 𝕜 × 𝕜), (eigenspace B i.1 ⊓ eigenspace A i.2) = ⊤ := by
    rw [← Two]
    exact exhaust hA hB hAB
  have Four : (⨆ (i : 𝕜 × 𝕜), (eigenspace B i.1 ⊓ eigenspace A i.2))ᗮ = ⊥ := by
    simp only [Submodule.orthogonal_eq_bot_iff, Three]
  exact (OrthogonalFamily.isInternal_iff One).mpr Four

universe u

variable {n m : Type u} [Fintype n] [Fintype m] (T : n → (E →ₗ[𝕜] E))
    (hT :(∀ (i : n), ((T i).IsSymmetric)))
    (hC : (∀ (i j : n), (T i) ∘ₗ (T j) = (T j) ∘ₗ (T i)))

open Classical

theorem eigenspace_of_subsingleton_nonempty [Subsingleton n] (h : Nonempty n) :
    ∃ (S : E →ₗ[𝕜] E), S.IsSymmetric ∧ (∀ (γ : n → 𝕜), (∀ (i : n),
    (eigenspace (T i) (γ i) = eigenspace S (γ i)))) := by
  have h0 : ∃ (S : E →ₗ[𝕜] E), S.IsSymmetric ∧ (∀ (i : n), T i = S) := by
    have i := choice h
    have H : (∀ (i j : n), T j  = T i) := by
      intro i _ ; rw [Subsingleton.allEq i _]
    use (T i)
    constructor
    · exact hT i
    · exact fun i_1 ↦ H i i_1
  obtain ⟨S , hS⟩ := h0
  use S
  constructor
  · exact hS.1
  · have h1 : (∀ (i : n), T i = S) → (∀ (γ : n → 𝕜), (∀ (i : n),
    (eigenspace (T i) (γ i) = eigenspace S (γ i)))) :=
     fun a γ i ↦ congrFun (congrArg eigenspace (a i)) (γ i)
    exact h1 hS.2

/-This has been moved via PR #14833-/
theorem eq_iff_orthogonalComplement_eq {K L : Submodule 𝕜 E} : K = L ↔ Kᗮ = Lᗮ := by
   constructor
   · exact fun a ↦ congrArg Submodule.orthogonal a
   · intro H
     rw [← (Submodule.orthogonal_orthogonal K), ← (Submodule.orthogonal_orthogonal) L]
     exact congrArg Submodule.orthogonal H

/--The following result is auxiliary, and not meant to be used outside this file. It forms
the base case of the induction proof of `orthogonalComplement_iSup_iInf_eigenspaces_eq_bot`-/
theorem orthogonalComplement_iSup_iInf_eigenspaces_eq_bot_base [Subsingleton n]:
    (⨆ (γ : n → 𝕜), (⨅ (j : n), (eigenspace (T j) (γ j)) : Submodule 𝕜 E))ᗮ = ⊥ := by
  by_cases case : Nonempty n
  · obtain ⟨S, hS⟩ := eigenspace_of_subsingleton_nonempty T hT case
    have h1 : (⨆ (γ : n → 𝕜), (⨅ (j : n), (eigenspace S (γ j)) : Submodule 𝕜 E))
        = (⨆ t, eigenspace S t) := by
      have h2 : ∀ (K : Submodule 𝕜 E), ((∀ (a : n → 𝕜), ⨅ j, eigenspace S (a j) ≤ K) ↔
        (∀ (b : 𝕜), eigenspace S b ≤ K)) := by
        intro K
        constructor
        · intro H b
          have := H (Function.const n b)
          simpa only [ge_iff_le, Function.const_apply, ciInf_const]
        · intro h f
          have c := choice case
          have A := eq_const_of_subsingleton f c; have := h (f c); rw [A]
          simpa only [Function.const_apply, ciInf_const, ge_iff_le]
      ext F
      simp only [iSup, sSup, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
          Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter,
          SetLike.mem_coe] at *
      constructor
      · intro hF i hi
        have I : ∀ (a : 𝕜), eigenspace S a ≤ i := fun a ↦ hi a
        rw [← h2] at I; apply hF; exact I
      · intro hF i hi
        have I : ∀ (a : n → 𝕜), ⨅ j, eigenspace S (a j) ≤ i := fun a ↦ hi fun j ↦ a j
        rw [h2] at I; apply hF; exact I
    simp only [hS]
    rw [← orthogonalComplement_iSup_eigenspaces_eq_bot hS.1]
    apply eq_iff_orthogonalComplement_eq.mpr
    simp only [Submodule.orthogonal_orthogonal, Submodule.mk.injEq, AddSubmonoid.mk.injEq,
      AddSubsemigroup.mk.injEq]; exact h1
  · simp only [not_nonempty_iff] at case
    simp only [iInf_of_empty, ciSup_unique, Submodule.top_orthogonal_eq_bot]

theorem invariance_iInf [Nonempty n] {S : E →ₗ[𝕜] E} (h : ∀ (i : n), (T i) ∘ₗ S = S ∘ₗ (T i)) :
    ∀ γ : n → 𝕜, ∀ v ∈ (⨅ (i : n), eigenspace (T i) (γ i)),
    S v ∈ (⨅ (i : n), eigenspace (T i) (γ i)) := by
  intro γ v hv
  simp only [Submodule.mem_iInf] at *
  intro i
  exact eigenspace_invariant (h i) (γ i) v (hv i)

theorem invariance_iInf' [Nonempty n] (i : n) :
    ∀ γ : {x // i ≠ x} → 𝕜, ∀ v ∈ (⨅ (j : {x // i ≠ x}), eigenspace ((Subtype.restrict (fun x ↦ i ≠ x) T) j) (γ j)),
    (T i) v ∈ (⨅ (j : {x // i ≠ x}), eigenspace ((Subtype.restrict (fun x ↦ i ≠ x) T) j) (γ j)) := by
  intro γ v hv
  simp only [Submodule.mem_iInf] at *
  exact fun i_1 ↦ eigenspace_invariant (hC (↑i_1) i) (γ i_1) v (hv i_1)

theorem invariance_iInf'' [Nonempty n] (i : n) :
    ∀ γ : n → 𝕜, ∀ v ∈ (⨅ (j : n), eigenspace (T j) (γ j)),
    (T i) v ∈ (⨅ (j : n), eigenspace (T j) (γ j)) := by
  intro γ v hv
  simp only [Submodule.mem_iInf] at *
  exact fun i_1 ↦ eigenspace_invariant (hC i_1 i) (γ i_1) v (hv i_1)

theorem inf_restrict' [Nonempty n] (i : n) (γ : {x // i ≠ x} → 𝕜) :
    (⨆ (μ : 𝕜) , eigenspace ((T i).restrict
    ((invariance_iInf' T hC i γ))) μ)ᗮ = ⊥ := by
  exact (LinearMap.IsSymmetric.restrict_invariant (hT i)
    (invariance_iInf' T hC i γ)).orthogonalComplement_iSup_eigenspaces_eq_bot

@[simp]
theorem inf_restrict'' [Nonempty n] (i : n) (γ : {x // i ≠ x} → 𝕜) :
    (⨆ (μ : 𝕜) , eigenspace ((T i).restrict
    ((invariance_iInf' T hC i γ))) μ) = ⊤ := by
  exact
    pre_exhaust fun x y ↦
      hT i ((⨅ j, eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j)).subtype x) ↑y

theorem inf_restrict''' [Nonempty n] (i : n) (γ : {x // i ≠ x} → 𝕜) :
    Submodule.map (Submodule.subtype (⨅ j, eigenspace (Subtype.restrict
    (fun x ↦ i ≠ x) T j) (γ j))) (⨆ (μ : 𝕜) , eigenspace ((T i).restrict
    ((invariance_iInf' T hC i γ))) μ) = Submodule.map (Submodule.subtype (⨅ j, eigenspace
    (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j))) ⊤ := by
  congr!
  congr!
  exact inf_restrict'' T hT hC i fun j ↦ γ j

theorem index_convert (i : n) [Nonempty n] (μ : 𝕜) (γ : {x // i ≠ x} → 𝕜) : (eigenspace (T i) μ ⊓
    (⨅ (j : {x // i ≠ x}), eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j))) =
    Submodule.map (Submodule.subtype ((⨅ (j : {x // i ≠ x}), eigenspace (T j) (γ j))))
    (eigenspace ((T i).restrict ((invariance_iInf' T hC i γ))) μ) := by
  ext v
  constructor
  · intro h
    simp only [ne_eq, Submodule.mem_inf, Submodule.mem_iInf, Subtype.forall] at h
    obtain ⟨A, B⟩ := h
    simp only [ne_eq, Submodule.mem_map, Subtype.exists, Submodule.mem_iInf, Subtype.forall]
    use v
    use B
    constructor
    · ext
      simp only [sub_apply, Module.algebraMap_end_apply, SetLike.mk_smul_mk,
        AddSubgroupClass.coe_sub, restrict_coe_apply, ZeroMemClass.coe_zero]
      exact A
    · rfl
  · intro h
    constructor
    · simp only [ne_eq, Submodule.mem_map, Subtype.exists, Submodule.mem_iInf, Subtype.forall] at h
      obtain ⟨w, hw, A, B⟩ := h
      simp only [SetLike.mem_coe, eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply]
      simp only [eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply, SetLike.mk_smul_mk] at A
      rw [← B]
      exact
        (AddSubmonoid.mk_eq_zero
              (⨅ j,
                    ker
                      (Subtype.restrict (fun x ↦ ¬i = x) T j -
                        (algebraMap 𝕜 (Module.End 𝕜 E)) (γ j))).toAddSubgroup.toAddSubmonoid).mp
          A
    · simp only [ne_eq, Submodule.iInf_coe, Set.mem_iInter, SetLike.mem_coe, Subtype.forall]
      intro j hj
      simp only [eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply] at *
      simp only [ne_eq, Submodule.mem_map, mem_ker, sub_apply, Module.algebraMap_end_apply,
        Subtype.exists, SetLike.mk_smul_mk, Submodule.mem_iInf, Subtype.forall] at h
      obtain ⟨w, hw, _, B⟩ := h
      rw [← B]
      exact hw j hj

theorem index_eigen_extend (i : n) [Nonempty n] (γ : {x // i ≠ x} → 𝕜) (μ : 𝕜) (x : E) :
    x ∈ Submodule.map (Submodule.subtype (⨅ (j: {x // i ≠ x}), eigenspace (T ↑j) (γ j)))
    (eigenspace ((T i).restrict ((invariance_iInf' T hC i γ))) μ) →
    x ∈ (⨅ (j : {x // i ≠ x}), eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j)) := by
  intro h
  simp only [ne_eq, Submodule.mem_map, Subtype.exists, Submodule.mem_iInf, Subtype.forall] at *
  intro a b
  obtain ⟨a', ⟨ha, ⟨_, h2⟩⟩⟩ := h
  rw [← h2]
  exact ha a b

theorem ext_experiment (i : n) [Nonempty n] (γ : {x // i ≠ x} → 𝕜) : ∀ x,
    x ∈ (⨆ (μ : 𝕜) , eigenspace ((T i).restrict ((invariance_iInf' T hC i γ))) μ) ↔
    x ∈ (⊤ : Submodule 𝕜 ↥(⨅ j, eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j))) := by
  have H := inf_restrict'' T hT hC i γ
  simp only [ne_eq, H, Submodule.mem_top, implies_true]

@[simp]
theorem ultra_silly_lemma (i : n) [Nonempty n] (γ : {x // i ≠ x} → 𝕜) :
    (⨅ (j : {x // i ≠ x}), eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j)) =
    (⨅ (j : {x // i ≠ x}), eigenspace (T j) (γ j)) := rfl

theorem indexing_nonsense0 (i : n) [Nontrivial n] (γ : n → 𝕜) :
     ⨅ (j : n), eigenspace (T j) (γ j) = (eigenspace (T i) (γ i)) ⊓
     ⨅ (j : {x // i ≠ x}), eigenspace (T j) (γ j) := by
  ext v
  constructor
  · intro h
    constructor
    · simp [iInf, sInf] at h
      exact h i
    · simp [iInf, sInf] at *
      exact fun i_1 _ ↦ h i_1
  · intro h
    simp [iInf, sInf]
    intro k
    by_cases H : k = i
    · rw [H]
      exact h.1
    · have F := h.2
      simp only [ne_eq, Submodule.iInf_coe, Set.mem_iInter, SetLike.mem_coe, Subtype.forall] at F
      exact F k fun a ↦ H (_root_.id (Eq.symm a))


theorem indexing_nonsense (i : n) [Nontrivial n] : ⨆ (γ : n → 𝕜), ⨅ j : n, eigenspace (T j) (γ j)
    = (⨆ (γ : {x // i ≠ x} → 𝕜), (⨆ μ : 𝕜, (eigenspace (T i) μ ⊓
    (⨅ (j : {x // i ≠ x}), eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j))))) := by
  ext v
  constructor
  · intro h
    simp only [ne_eq, ultra_silly_lemma]
    conv =>
     rhs
     rw [iSup]
    simp only [sSup, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, iSup_le_iff,
      Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter,
      SetLike.mem_coe]
    intro K
    rw [iSup] at h
    simp only [sSup, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter, SetLike.mem_coe] at h
    intro H
    apply h K
    intro a w hw
    rw [indexing_nonsense0 T (i := i) (γ := a)] at hw
    simp only [ne_eq, Submodule.mem_inf] at hw
    have : ∀ (a : n → 𝕜), ⨅ j, eigenspace (T j) (a j) ≤ K := by
      intro f
      rw [indexing_nonsense0 T i]
      apply H
    exact H (fun j ↦ a ↑j) (a i) hw
  · intro h
    simp only [ne_eq, ultra_silly_lemma] at h
    rw [iSup] at *
    simp only [sSup, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter, SetLike.mem_coe] at *
    intro K hK
    have A : ∀ (a : {x // ¬i = x} → 𝕜), ⨆ μ, eigenspace (T i) μ ⊓
        ⨅ (j : {x // i ≠ x}), eigenspace (T ↑j) (a j) ≤ K := by
      intro γ' v hgv
      simp only [iSup, sSup, ne_eq, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
        Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter,
        SetLike.mem_coe] at hgv
      have B : ∀ (μ : 𝕜), eigenspace (T i) μ ⊓ ⨅ (j : {x // i ≠ x}), eigenspace (T ↑j) (γ' j) ≤ K := by
        intro μ
        let γ : n → 𝕜 := Set.piecewise (fun x ↦ i ≠ x) (Function.extend Subtype.val γ' 1)
          (Function.const n μ)
        have C1 : γ i = μ := Set.piecewise_eq_of_not_mem (fun x ↦ i ≠ x) (Function.extend Subtype.val γ' 1)
            (Function.const n μ) fun a ↦ a rfl
        have C2 : ∀ (j : {x // i ≠ x}), γ j = γ' j:= by
          intro j
          have := j.2
          simp only [ne_eq, Subtype.coe_prop, Set.piecewise_eq_of_mem, γ]
          refine Function.Injective.extend_apply ?hf γ' _ j
          exact Subtype.val_injective
        have C : eigenspace (T i) μ ⊓ ⨅ (j : {x // i ≠ x}), eigenspace (T ↑j) (γ' j)
            = eigenspace (T i) (γ i) ⊓ ⨅ (j : {x // i ≠ x}), eigenspace (T ↑j) (γ j) := by
          congr!
          exact _root_.id (Eq.symm C1)
          congr!
          simp only [ne_eq, C2]
        rw [C]
        rw [← indexing_nonsense0]
        exact hK fun j ↦ γ j
      apply hgv
      exact B
    exact h K A

/-This is just index_convert, so we can probably remove later.-/
theorem indexed_matching (i : n) [Nonempty n] (γ : {x // i ≠ x} → 𝕜) (μ : 𝕜) :
   Submodule.map (Submodule.subtype (⨅ (j: {x // i ≠ x}), eigenspace (T ↑j) (γ j)))
      (eigenspace ((T i).restrict ((invariance_iInf' T hC i γ))) μ)
       = (eigenspace (T i) μ ⊓ ⨅ j, eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j)) := by
  rw [← index_convert T hC i μ fun j ↦ γ j]

theorem prelim_sub_exhaust (i : n) [Nontrivial n] (γ : {x // i ≠ x} → 𝕜) :
    ⨆ μ, Submodule.map (⨅ (j: {x // i ≠ x}), eigenspace (T ↑j) (γ j)).subtype
    (eigenspace ((T i).restrict ((invariance_iInf' T hC i γ))) μ) =
    (⨅ (j : {x // i ≠ x}), eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j)) := by
  simp only [iSup, sSup, ne_eq, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  ext v
  constructor
  · intro h
    simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter,
      SetLike.mem_coe] at h
    simp only [iInf, sInf, Set.mem_range, Subtype.exists, Set.iInter_exists, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter, SetLike.mem_coe]
    intro K j hj HH
    apply h
    rw [← HH]
    intro a w hw
    simp only [iInf, sInf, Submodule.mem_map, Subtype.exists, Set.mem_range, Set.iInter_exists,
      Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_iInter,
      SetLike.mem_coe] at hw
    obtain ⟨a, ⟨ha, hb⟩⟩ := hw
    rw [← hb.2]
    exact ha (eigenspace (Subtype.restrict (fun x ↦ ¬i = x) T ⟨j, hj⟩) (γ ⟨j, hj⟩)) j hj rfl
  · have B := inf_restrict''' T hT hC i γ
    simp only [Submodule.mem_iInf, Subtype.forall, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_iInter, SetLike.mem_coe]
    intro h F hH
    have hH1 : ∀ (a : 𝕜), Submodule.map (⨅ (j : {x // i ≠ x}) , eigenspace (T ↑j) (γ j)).subtype
        (eigenspace ((T i).restrict ((invariance_iInf' T hC i γ))) a) ≤ F := by exact fun a ↦ hH a
    simp only [ne_eq, ultra_silly_lemma, Submodule.map_iSup, Submodule.map_top,
      Submodule.range_subtype] at B
    have RR : (⨆ μ : 𝕜, Submodule.map (⨅ (j : {x // i ≠ x}), eigenspace (T ↑j) (γ j)).subtype
        (eigenspace ((T i).restrict ((invariance_iInf' T hC i γ))) μ)) ≤ F := by
      simp only [ne_eq, ultra_silly_lemma, iSup_le_iff, hH1, implies_true]
    rw [B] at RR
    have Final : v ∈ ⨅ (j: {x // i ≠ x}), eigenspace (T ↑j) (γ j) := (Submodule.mem_iInf
      fun (i_1 : {x // i ≠ x}) ↦ eigenspace (T ↑i_1) (γ i_1)).mpr fun i_1 ↦ h (↑i_1) i_1.property
    exact RR Final

theorem index_post_exhaust (i : n) [Nontrivial n] :
    (⨆ (γ : {x // i ≠ x} → 𝕜), (⨆ μ : 𝕜, (eigenspace (T i) μ ⊓ (⨅ (j : {x // i ≠ x}),
    eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j))))) = ⨆ (γ : {x // i ≠ x} → 𝕜),
    (⨅ (j : {x // i ≠ x}), eigenspace (Subtype.restrict (fun x ↦ i ≠ x) T j) (γ j)) := by
  simp only [ne_eq, Submodule.orthogonal_eq_bot_iff]
  conv =>
   lhs
   rhs
   ext γ
   rhs
   ext μ
   rw [index_convert T hC i]
  conv =>
   lhs
   rhs
   ext γ
   rw [prelim_sub_exhaust T hT hC]

theorem orthogonalComplement_iSup_iInf_eigenspaces_eq_bot:
    (⨆ (γ : n → 𝕜), (⨅ (j : n), (eigenspace (T j) (γ j)) : Submodule 𝕜 E))ᗮ = ⊥ := by
  revert T
  refine' Fintype.induction_subsingleton_or_nontrivial n _ _
  · intro m _ hhm T hT _
    exact orthogonalComplement_iSup_iInf_eigenspaces_eq_bot_base T hT
  · intro m hm hmm H T hT hC
    obtain ⟨i, _ , _ ⟩ := exists_pair_ne m
    have C : Fintype.card { x // i ≠ x } < Fintype.card m := by
      simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_ofSubsingleton,
      tsub_lt_self_iff, zero_lt_one, and_true]
      exact Fintype.card_pos
    have D := H {x // i ≠ x} C (Subtype.restrict (fun x ↦ i ≠ x) T)
      (fun (i_1 : {x // i ≠ x}) ↦ hT ↑i_1) (fun (i_1 j : { x // i ≠ x }) ↦ hC ↑i_1 ↑j)
    simp only [Submodule.orthogonal_eq_bot_iff] at *
    rw [← index_post_exhaust] at D
    rw [indexing_nonsense]
    exact D
    exact fun i ↦ hT i
    exact hC

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
