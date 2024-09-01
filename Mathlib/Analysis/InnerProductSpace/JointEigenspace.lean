/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Joint eigenspaces of a commuting pair of symmetric operators

NEED TO UPDATE ALL OF THIS FOR TUPLES!!!
ALSO RENAMING RESULTS BELOW IN ACCORDANCE WITH PAIR CHANGES, AND DOCSTRINGS.

This file collects various decomposition results for joint eigenspaces of a commuting pair
of symmetric operators on a finite-dimensional inner product space.

# Main Result

* `LinearMap.IsSymmetric.directSum_isInternal_of_commute` establishes that
   if `{A B : E →ₗ[𝕜] E}`, then `IsSymmetric A`, `IsSymmetric B` and `A ∘ₗ B = B ∘ₗ A` imply that
   `E` decomposes as an internal direct sum of the pairwise orthogonal spaces
   `eigenspace B μ ⊓ eigenspace A ν`

## TODO

Develop a `Diagonalization` structure for linear maps and / or matrices which consists of a basis,
and a proof obligation that the basis vectors are eigenvectors.

## Tags

self-adjoint operator, simultaneous eigenspaces, joint eigenspaces

-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open Module.End

namespace LinearMap

namespace IsSymmetric

section Pair

variable {α : 𝕜} {A B : E →ₗ[𝕜] E}

/--If a pair of operators commute, then the eigenspaces of one are invariant under the other.-/
theorem eigenspace_invariant_of_commute
    (hAB : A ∘ₗ B = B ∘ₗ A) (α : 𝕜) : ∀ v ∈ (eigenspace A α), (B v ∈ eigenspace A α) := by
  intro v hv
  rw [eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply, ← comp_apply A B v, hAB,
    comp_apply B A v, ← map_smul, ← map_sub, hv, map_zero] at *

/--The simultaneous eigenspaces of a pair of commuting symmetric operators form an
`OrthogonalFamily`.-/
theorem orthogonalFamily_eigenspace_inf_eigenspace (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
    (fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ) :=
     OrthogonalFamily.of_pairwise fun i j hij v ⟨hv1 , hv2⟩ ↦ by
    obtain (h₁ | h₂) : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hij
    all_goals intro w ⟨hw1, hw2⟩
    · exact hB.orthogonalFamily_eigenspaces.pairwise h₁ hv2 w hw2
    · exact hA.orthogonalFamily_eigenspaces.pairwise h₂ hv1 w hw1

open Submodule in

/-- The intersection of eigenspaces of commuting selfadjoint operators is equal to the eigenspace of
one operator restricted to the eigenspace of the other, which is an invariant subspace because the
operators commute. -/
theorem eigenspace_inf_eigenspace
    (hAB : A ∘ₗ B = B ∘ₗ A) (γ : 𝕜) :
    eigenspace A α ⊓ eigenspace B γ = map (Submodule.subtype (eigenspace A α))
      (eigenspace (B.restrict (eigenspace_invariant_of_commute hAB α)) γ) :=
  (eigenspace A α).inf_genEigenspace _ _ (k := 1)

variable [FiniteDimensional 𝕜 E]

/-- If A and B are commuting symmetric operators on a finite dimensional inner product space
then the eigenspaces of the restriction of B to any eigenspace of A exhaust that eigenspace.-/
theorem iSup_eigenspace_inf_eigenspace (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A):
    (⨆ γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α := by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  simp only [eigenspace_inf_eigenspace hAB, ← Submodule.map_iSup]
  congr 1
  rw [← Submodule.orthogonal_eq_bot_iff]
  exact orthogonalComplement_iSup_eigenspaces_eq_bot <|
    hB.restrict_invariant <| eigenspace_invariant_of_commute hAB α

/-- If A and B are commuting symmetric operators acting on a finite dimensional inner product space,
then the simultaneous eigenspaces of A and B exhaust the space. -/
theorem iSup_iSup_eigenspace_inf_eigenspace_eq_top (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A) :
    (⨆ α, ⨆ γ, eigenspace A α ⊓ eigenspace B γ) = ⊤ := by
  simpa [iSup_eigenspace_inf_eigenspace hB hAB] using
    Submodule.orthogonal_eq_bot_iff.mp <| hA.orthogonalComplement_iSup_eigenspaces_eq_bot

/-- Given a commuting pair of symmetric linear operators on a finite dimensional inner product
space, the space decomposes as an internal direct sum of simultaneous eigenspaces of these
operators. -/
theorem directSum_isInteral_of_commute (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A) :
    DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)):= by
  apply (orthogonalFamily_eigenspace_inf_eigenspace hA hB).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top hA hB hAB

end Pair

section Tuple

universe u

variable {n m : Type u} [Fintype m] (T : n → (E →ₗ[𝕜] E))
    (hT :(∀ (i : n), ((T i).IsSymmetric)))
   -- (hC : (∀ (i j : n), (T i) ∘ₗ (T j) = (T j) ∘ₗ (T i)))

open Classical

--imported the [Fintype n] and hC from above into the statement. More of this will have to happen
--below, but it may be finicky because we need to call all of these functions and the explicit
--arguments may be needed.

theorem invariance_iInf [Fintype n] [Nonempty n]
    (hC : (∀ (i j : n), (T i) ∘ₗ (T j) = (T j) ∘ₗ (T i))) (i : n) :
    ∀ γ : {x // x ≠ i} → 𝕜, ∀ v ∈ (⨅ (j : {x // x ≠ i}),
    eigenspace ((Subtype.restrict (fun x ↦ x ≠ i) T) j) (γ j)), (T i) v ∈ (⨅ (j : {x // x ≠ i}),
    eigenspace ((Subtype.restrict (fun x ↦ x ≠ i) T) j) (γ j)) := by
  intro γ v hv
  simp only [Submodule.mem_iInf] at *
  exact fun i_1 ↦ eigenspace_invariant_of_commute (hC (↑i_1) i) (γ i_1) v (hv i_1)

theorem iSup_iInf_fun_index_split_single {α β γ : Type*} [DecidableEq α] [CompleteLattice γ]
    (i : α) (s : α → β → γ) : (⨆ f : α → β, ⨅ x, s x (f x)) =
      ⨆ f' : {y // y ≠ i} → β, ⨆ y : β, s i y ⊓ ⨅ x' : {y // y ≠ i}, (s x' (f' x')) := by
  rw [← (Equiv.funSplitAt i β).symm.iSup_comp, iSup_prod, iSup_comm]
  congr!  with f' y
  rw [iInf_split_single _ i, iInf_subtype]
  congr! with x hx
  · simp
  · simp [dif_neg hx]

theorem invariant_subspace_eigenspace_exhaust [FiniteDimensional 𝕜 E] {F : Submodule 𝕜 E}
    (S : E →ₗ[𝕜] E) (hS: IsSymmetric S) (hInv : ∀ v ∈ F, S v ∈ F) : ⨆ μ, Submodule.map F.subtype
    (eigenspace (S.restrict hInv) μ)  = F := by
 conv_lhs => rw [← Submodule.map_iSup]
 conv_rhs => rw [← Submodule.map_subtype_top F]
 congr!
 have H : IsSymmetric (S.restrict hInv) := fun x y ↦ hS (F.subtype x) ↑y
 apply Submodule.orthogonal_eq_bot_iff.mp (H.orthogonalComplement_iSup_eigenspaces_eq_bot)

theorem orthogonalComplement_iSup_iInf_eigenspaces_eq_bot [Fintype n]
    (hT :(∀ (i : n), ((T i).IsSymmetric))):
    (⨆ (γ : n → 𝕜), (⨅ (j : n), (eigenspace (T j) (γ j)) : Submodule 𝕜 E))ᗮ = ⊥ := by
  revert T
  refine Fintype.induction_subsingleton_or_nontrivial n ?_ ?_
  · intro m _ hhm T hT
    simp only [Submodule.orthogonal_eq_bot_iff]
    by_cases case : Nonempty m
    · have i := choice case
      have := uniqueOfSubsingleton i
      conv => lhs; rhs; ext γ; rw [ciInf_subsingleton i]
      rw [← (Equiv.funUnique m 𝕜).symm.iSup_comp]
      apply Submodule.orthogonal_eq_bot_iff.mp ((hT i).orthogonalComplement_iSup_eigenspaces_eq_bot)
    · simp only [not_nonempty_iff] at case
      simp only [iInf_of_empty, ciSup_unique]
  · intro m hm hmm H T hT
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

theorem orthogonalFamily_iInf_eigenspaces
    (hT :(∀ (i : n), ((T i).IsSymmetric))) : OrthogonalFamily 𝕜 (fun (γ : n → 𝕜) =>
    (⨅ (j : n), (eigenspace (T j) (γ j)) : Submodule 𝕜 E))
    (fun (γ : n → 𝕜) => (⨅ (j : n), (eigenspace (T j) (γ j))).subtypeₗᵢ) := by
  intro f g hfg Ef Eg
  obtain ⟨a , ha⟩ := Function.ne_iff.mp hfg
  have H := (orthogonalFamily_eigenspaces (hT a) ha)
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.coeSubtype, Subtype.forall] at H
  apply H
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (f _)).mp Ef.2 _
  · exact (Submodule.mem_iInf <| fun _ ↦ eigenspace (T _) (g _)).mp Eg.2 _

/-- Given a finite commuting family of symmetric linear operators, the Hilbert space on which they
act decomposes as an internal direct sum of simultaneous eigenspaces. -/
theorem DirectSum.IsInternal_of_simultaneous_eigenspaces_of_commuting_symmetric_tuple [Fintype n]
    [FiniteDimensional 𝕜 E] (hT :(∀ (i : n), ((T i).IsSymmetric))) :
    DirectSum.IsInternal (fun (α : n → 𝕜) ↦ ⨅ (j : n), (eigenspace (T j) (α j))) := by
  rw [OrthogonalFamily.isInternal_iff]
  · exact orthogonalComplement_iSup_iInf_eigenspaces_eq_bot T hT
  · exact orthogonalFamily_iInf_eigenspaces T hT

end Tuple

end IsSymmetric

end LinearMap
