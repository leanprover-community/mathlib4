/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Joint eigenspaces of commuting symmetric operators

This file collects various decomposition results for joint eigenspaces of commuting
symmetric operators on a finite-dimensional inner product space.

# Main Result

* `LinearMap.IsSymmetric.directSum_isInternal_of_commute` establishes that
   if `{A B : E →ₗ[𝕜] E}`, then `IsSymmetric A`, `IsSymmetric B` and `A ∘ₗ B = B ∘ₗ A` imply that
   `E` decomposes as an internal direct sum of the pairwise orthogonal spaces
   `eigenspace B μ ⊓ eigenspace A ν`
* `LinearMap.IsSymmetric.directSum_isInternal_of_commute_of_fintype` establishes the
   analogous result to `LinearMap.IsSymmetric.directSum_isInternal_of_commute` for finite commuting
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
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coeSubtype, Subtype.forall] at H
  apply H
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (f _)).mp Ef.2 _
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (g _)).mp Eg.2 _

variable [FiniteDimensional 𝕜 E]

/-- If A and B are commuting symmetric operators on a finite dimensional inner product space
then the eigenspaces of the restriction of B to any eigenspace of A exhaust that eigenspace. -/
theorem iSup_eigenspace_inf_eigenspace (hB : B.IsSymmetric) (hAB : Commute A B) :
    (⨆ γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α := by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  simp only [← Module.End.genEigenspace_one B, ← Submodule.map_iSup,
    (eigenspace A α).inf_genEigenspace _ (mapsTo_genEigenspace_of_comm hAB α 1)]
  congr 1
  simpa only [Module.End.genEigenspace_one, Submodule.orthogonal_eq_bot_iff]
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

/-- The orthocomplement of the indexed supremum of joint eigenspaces of a finite commuting tuple of
symmetric operators is trivial. -/
theorem orthogonalComplement_iSup_iInf_eigenspaces_eq_bot [Finite n]
    (hT : ∀ i, (T i).IsSymmetric) (hC : ∀ i j, Commute (T i) (T j)) :
    (⨆ γ : n → 𝕜, ⨅ j, eigenspace (T j) (γ j))ᗮ = ⊥ := by
  have _ := Fintype.ofFinite n
  revert T
  change ∀ T, _
  refine Fintype.induction_subsingleton_or_nontrivial n (fun m _ hhm T hT _ ↦ ?_)
    (fun m hm hmm H T hT hC ↦ ?_)
  · obtain (hm | hm) := isEmpty_or_nonempty m
    · simp
    · have := uniqueOfSubsingleton (Classical.choice hm)
      simpa only [ciInf_unique, ← (Equiv.funUnique m 𝕜).symm.iSup_comp]
        using hT default |>.orthogonalComplement_iSup_eigenspaces_eq_bot
  · have i := Classical.arbitrary m
    classical
    specialize H {x // x ≠ i} (Fintype.card_subtype_lt (x := i) (by simp))
      (Subtype.restrict (· ≠ i) T) (hT ·) (hC · ·)
    simp only [Submodule.orthogonal_eq_bot_iff] at *
    rw [← (Equiv.funSplitAt i 𝕜).symm.iSup_comp, iSup_prod, iSup_comm]
    convert H with γ
    rw [← iSup_eigenspace_restrict (T i) (hT i) (F := ⨅ j, eigenspace _ _)]
    swap
    · exact mapsTo_iInf_genEigenspace_of_forall_comm (fun j : {j // j ≠ i} ↦ hC j i) γ 1
    congr! with μ
    rw [← Module.End.genEigenspace_one, ← Submodule.inf_genEigenspace _ _ _ (k := 1), inf_comm,
      iInf_split_single _ i, iInf_subtype]
    congr! with x hx
    · simp
    · simp [dif_neg hx]

/-- Given a finite commuting family of symmetric linear operators, the Hilbert space on which they
act decomposes as an internal direct sum of simultaneous eigenspaces. -/
theorem LinearMap.IsSymmetric.directSum_isInternal_of_commute_of_fintype [Finite n]
    [DecidableEq (n → 𝕜)] (hT :∀ i, (T i).IsSymmetric)
    (hC : ∀ i j, Commute (T i) (T j)) :
    DirectSum.IsInternal (fun α : n → 𝕜 ↦ ⨅ j, eigenspace (T j) (α j)) := by
  rw [OrthogonalFamily.isInternal_iff]
  · exact orthogonalComplement_iSup_iInf_eigenspaces_eq_bot hT hC
  · exact orthogonalFamily_iInf_eigenspaces hT

end RCLike

open Module End

lemma iSup_iInf_maxGenEigenspace_eq_top_of_commute {ι K V : Type*}
    [Finite ι] [Field K] [DecidableEq K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : ι → End K V) (h : Pairwise fun i j ↦ Commute (f i) (f j))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  have _ := Fintype.ofFinite ι
  revert f
  refine Fintype.induction_subsingleton_or_nontrivial ι (fun m _ hhm f hf x ↦ ?_)
    (fun m hm hmm H f hf hC ↦ ?_)
  · obtain (hm | hm) := isEmpty_or_nonempty m
    · simp
    · have := uniqueOfSubsingleton (Classical.choice hm)
      simpa [ciInf_unique, ← (Equiv.funUnique m K).symm.iSup_comp] using x default
  · have i := Classical.arbitrary m
    classical
    specialize H {x // x ≠ i} (Fintype.card_subtype_lt (x := i) (by simp))
     (Subtype.restrict (· ≠ i) f) (fun _ _ _ ↦ hf <| by simpa [Subtype.coe_ne_coe]) (hC ·)
    rw [← (Equiv.funSplitAt i K).symm.iSup_comp, iSup_prod, iSup_comm]
    convert H with γ
    rw [← iSup_eigenspace_restrict (f i) (hf i) (F := ⨅ j, eigenspace _ _)]
    swap
    · exact mapsTo_iInf_genEigenspace_of_forall_comm (fun j : {j // j ≠ i} ↦ hC j i) γ 1
    congr! with μ
    rw [← Module.End.genEigenspace_one, ← Submodule.inf_genEigenspace _ _ _ (k := 1), inf_comm,
      iInf_split_single _ i, iInf_subtype]
    congr! with x hx
    · simp
    · simp [dif_neg hx]

end IsSymmetric

end LinearMap
