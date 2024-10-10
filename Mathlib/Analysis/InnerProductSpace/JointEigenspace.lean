/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Joint eigenspaces of commuting symmetric operators

This file collects various decomposition results for joint eigenspaces of commuting
symmetric operators on a finite-dimensional inner product space.

# Main Result

* `LinearMap.IsSymmetric.directSum_isInternal_of_commute` establishes that in finite dimensions
   if `{A B : E →ₗ[𝕜] E}`, then `IsSymmetric A`, `IsSymmetric B` and `A ∘ₗ B = B ∘ₗ A` imply that
   `E` decomposes as an internal direct sum of the pairwise orthogonal spaces
   `eigenspace B μ ⊓ eigenspace A ν`
* `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute` establishes that in finite dimensions,
   the indexed supremum of the joint eigenspaces of a commuting tuple of symmetric linear operators
   equals `⊤`
* `LinearMap.IsSymmetric.directSum_isInternal_of_commute_of_fintype` establishes the
   analogous result to `LinearMap.IsSymmetric.directSum_isInternal_of_commute` for commuting
   tuples of symmetric operators.

## TODO

Develop a `Diagonalization` structure for linear maps and / or matrices which consists of a basis,
and a proof obligation that the basis vectors are eigenvectors.

## Tags

symmetric operator, simultaneous eigenspaces, joint eigenspaces

-/

open Module.End

namespace LinearMap

namespace IsSymmetric

variable {𝕜 E n m : Type*}

open Submodule

section RCLike

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {α : 𝕜} {A B : E →ₗ[𝕜] E} {T : n → E →ₗ[𝕜] E}

/-- The joint eigenspaces of a pair of commuting symmetric operators form an
`OrthogonalFamily`. -/
theorem orthogonalFamily_eigenspace_inf_eigenspace (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
    (fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ) :=
     OrthogonalFamily.of_pairwise fun i j hij v ⟨hv1 , hv2⟩ ↦ by
    obtain (h₁ | h₂) : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hij
    all_goals intro w ⟨hw1, hw2⟩
    · exact hB.orthogonalFamily_eigenspaces.pairwise h₁ hv2 w hw2
    · exact hA.orthogonalFamily_eigenspaces.pairwise h₂ hv1 w hw1

/-- The joint eigenspaces of a tuple of commuting symmetric operators form an
`OrthogonalFamily`. -/
theorem orthogonalFamily_iInf_eigenspaces
    (hT : ∀ i, (T i).IsSymmetric) :
    OrthogonalFamily 𝕜 (fun γ : n → 𝕜 ↦ (⨅ j, eigenspace (T j) (γ j) : Submodule 𝕜 E))
      fun γ : n → 𝕜 ↦ (⨅ j, eigenspace (T j) (γ j)).subtypeₗᵢ := by
  intro f g hfg Ef Eg
  obtain ⟨a , ha⟩ := Function.ne_iff.mp hfg
  have H := (orthogonalFamily_eigenspaces (hT a) ha)
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, Subtype.forall] at H
  apply H
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (f _)).mp Ef.2 _
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (g _)).mp Eg.2 _

variable [FiniteDimensional 𝕜 E]

/-- If A and B are commuting symmetric operators on a finite dimensional inner product space
then the eigenspaces of the restriction of B to any eigenspace of A exhaust that eigenspace. -/
theorem iSup_eigenspace_inf_eigenspace (hB : B.IsSymmetric) (hAB : Commute A B) :
    (⨆ γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α := by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  have H : ∀ μ, genEigenspace B μ 1 = eigenspace B μ := fun μ ↦ rfl
  simp only [← H, ← Submodule.map_iSup,
    (eigenspace A α).inf_genEigenspace _ (mapsTo_genEigenspace_of_comm hAB α 1)]
  congr 1
  simpa only [H, Submodule.orthogonal_eq_bot_iff]
    using orthogonalComplement_iSup_eigenspaces_eq_bot <|
      hB.restrict_invariant <| mapsTo_genEigenspace_of_comm hAB α 1

/-- If A and B are commuting symmetric operators acting on a finite dimensional inner product space,
then the simultaneous eigenspaces of A and B exhaust the space. -/
theorem iSup_iSup_eigenspace_inf_eigenspace_eq_top (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : Commute A B) :
    (⨆ α, ⨆ γ, eigenspace A α ⊓ eigenspace B γ) = ⊤ := by
  simpa [iSup_eigenspace_inf_eigenspace hB hAB] using
    Submodule.orthogonal_eq_bot_iff.mp <| hA.orthogonalComplement_iSup_eigenspaces_eq_bot

/-- Given a commuting pair of symmetric linear operators on a finite dimensional inner product
space, the space decomposes as an internal direct sum of simultaneous eigenspaces of these
operators. -/
theorem directSum_isInternal_of_commute (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : Commute A B) :
    DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)):= by
  apply (orthogonalFamily_eigenspace_inf_eigenspace hA hB).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top hA hB hAB

/-- If `F` is an invariant subspace of a symmetric operator `S`, then `F` is the supremum of the
eigenspaces of the restriction of `S` to `F`. -/
theorem iSup_eigenspace_restrict {F : Submodule 𝕜 E}
    (S : E →ₗ[𝕜] E) (hS : IsSymmetric S) (hInv : Set.MapsTo S F F) :
    ⨆ μ, map F.subtype (eigenspace (S.restrict hInv) μ) = F := by
  conv_lhs => rw [← Submodule.map_iSup]
  conv_rhs => rw [← map_subtype_top F]
  congr!
  have H : IsSymmetric (S.restrict hInv) := fun x y ↦ hS (F.subtype x) y
  apply orthogonal_eq_bot_iff.mp (H.orthogonalComplement_iSup_eigenspaces_eq_bot)

/-- In finite dimensions, the indexed supremum of joint `maxGenEigenspaces` of a finite tuple of
commuting operators equals `⊤` provided the indexed supremum of `maxGenEigenspaces` of each
operator in the tuple equals `⊤`. -/
theorem iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute {ι K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : ι → Module.End K V) (h : Pairwise fun i j ↦ Commute (f i) (f j))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
    (fun i j ↦ Module.End.mapsTo_maxGenEigenspace_of_comm ?_) h'
  rcases eq_or_ne j i with rfl | hij <;> tauto

/-- Every generalized eigenspace of a symmetric operator is an eigenspace. -/
theorem genEigenspace_eq_eigenspace
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ} {μ : 𝕜} (hn : 1 ≤ n) :
    genEigenspace T μ n = genEigenspace T μ 1 := by
  refine Nat.le_induction rfl (fun k hk ih ↦ ?_) n hn
  refine ih ▸ le_antisymm (fun x hx ↦ ?_) ((genEigenspace T μ).mono k.le_succ)
  obtain (rfl | hx_ne) := eq_or_ne x 0
  · exact zero_mem _
  · have hμ : HasEigenvalue T μ := hasEigenvalue_of_hasGenEigenvalue (k := k + 1) <|
      (genEigenspace T μ (k + 1)).ne_bot_iff.mpr ⟨x, hx, hx_ne⟩
    have hT' := LinearMap.isSymmetric_iff_isSelfAdjoint T |>.mp hT
    have hTμ : ((T - μ • 1) ^ k).IsSymmetric  := by
      rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      refine .pow (hT'.sub (.smul ?_ ?_)) k
      · exact hT.conj_eigenvalue_eq_self hμ
      · exact (LinearMap.isSymmetric_iff_isSelfAdjoint 1).mp LinearMap.IsSymmetric.id
    rw [mem_genEigenspace, ← norm_eq_zero, ← sq_eq_zero_iff, norm_sq_eq_inner (𝕜 := 𝕜)]
    rw [hTμ, ← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, ← pow_add]
    simp [mem_genEigenspace .. |>.mp <| (genEigenspace T μ).mono (show k + 1 ≤ k + k by gcongr) hx]

lemma maxGenEigenspace_eq_eigenspace
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {μ : 𝕜} :
    maxGenEigenspace T μ = eigenspace T μ := calc
  _ = ⨆ n, genEigenspace T μ (n + 1) := by
    rw [maxGenEigenspace_def, ← sup_iSup_nat_succ, genEigenspace_def]; simp [LinearMap.one_eq_id]
  _ = ⨆ _ : ℕ, genEigenspace T μ 1 := by
    congr! 2 with n; exact genEigenspace_eq_eigenspace hT n.succ_pos
  _ = eigenspace T μ := by simp [genEigenspace_def, eigenspace_def]

/-- In finite dimensions, the indexed supremum of the joint eigenspaces of a commuting tuple of
symmetric linear operators equals `⊤`. -/
theorem iSup_iInf_eq_top_of_commute {ι : Type*}
    (T : ι → E →ₗ[𝕜] E) (hT : ∀ i, (T i).IsSymmetric) (h : Pairwise fun i j ↦ Commute (T i) (T j)):
    ⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i) (χ i) = ⊤ := calc
  _ = ⨆ χ : ι → 𝕜, ⨅ i, maxGenEigenspace (T i) (χ i) :=
    congr(⨆ χ : ι → 𝕜, ⨅ i, $((hT i).maxGenEigenspace_eq_eigenspace.symm))
  _ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T h fun i ↦ by
    rw [← orthogonal_eq_bot_iff, congr(⨆ μ, $((hT i).maxGenEigenspace_eq_eigenspace)),
      (hT i).orthogonalComplement_iSup_eigenspaces_eq_bot]

/-- In finite dimensions, given a finite commuting family of symmetric linear operators, the inner
product space on which they act decomposes as an internal direct sum of joint eigenspaces. -/
theorem LinearMap.IsSymmetric.directSum_isInternal_of_commute_of_fintype [Fintype n]
    (hT :∀ i, (T i).IsSymmetric) (hC : ∀ i j, Commute (T i) (T j)) :
    DirectSum.IsInternal (fun α : n → 𝕜 ↦ ⨅ j, eigenspace (T j) (α j)) := by
  rw [OrthogonalFamily.isInternal_iff]
  · rw [iSup_iInf_eq_top_of_commute _ hT fun ⦃_ _⦄ _ ↦ hC _ _, top_orthogonal_eq_bot]
  · exact orthogonalFamily_iInf_eigenspaces hT

end RCLike

end IsSymmetric

end LinearMap
