/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Simultaneous eigenspaces of a commuting pair of symmetric operators

This file collects various decomposition results for simultaneous eigenspaces of a commuting pair
of symmetric operators on a finite-dimensional inner product space.

# Main Result

* `DirectSum.IsInternal.eigenspaces_of_commuting_symmetric_pair` establishes that
   if `{A B : E →ₗ[𝕜] E}`, then `IsSymmetric A`, `IsSymmetric B` and `A ∘ₗ B = B ∘ₗ A` imply that
   `E` decomposes as an internal direct sum of the pairwise orthogonal spaces
   `eigenspace B μ ⊓ eigenspace A ν`

## TODO

Develop a `Diagonalization` structure for linear maps and / or matrices which consists of a basis,
and a proof obligation that the basis vectors are eigenvectors.

## Tags

self-adjoint operator, simultaneous eigenspaces, simultaneous diagonalization

-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open Module.End

namespace LinearMap

namespace IsSymmetric

section Pair

variable {α : 𝕜} {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A)

/--If a pair of operators commute, then the eigenspaces of one are invariant under the other.-/
theorem eigenspace_invariant_of_commute (α : 𝕜) :
    ∀ v ∈ (eigenspace A α), (B v ∈ eigenspace A α) := by
  intro v hv
  rw [eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply, ← comp_apply A B v, hAB,
  comp_apply B A v, ← map_smul, ← map_sub, hv, map_zero] at *

/--The inf of an eigenspace of an operator with another invariant subspace
agrees with the corresponding eigenspace of the restriction of that operator to the
invariant subspace-/
theorem eigenspace_restrict_eigenspace_eq_inf : (fun (γ : 𝕜) ↦
    Submodule.map (Submodule.subtype (eigenspace A α)) (eigenspace (B.restrict
    (eigenspace_invariant_of_commute hAB α)) γ))
    = (fun (γ : 𝕜) ↦ (eigenspace A α ⊓ eigenspace B γ)) := by
  funext γ
  exact Eq.symm (Submodule.inf_genEigenspace B (eigenspace A α)
    (eigenspace_invariant_of_commute hAB α) (μ := γ) (k := 1))

/-- If A and B are commuting symmetric operators on a finite dimensional inner product space
then the eigenspaces of the restriction of B to any eigenspace of A exhaust that eigenspace.-/
theorem iSup_inf_eq_top: (⨆ γ , (eigenspace (LinearMap.restrict B
    (eigenspace_invariant_of_commute hAB α)) γ)) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    exact orthogonalComplement_iSup_eigenspaces_eq_bot (LinearMap.IsSymmetric.restrict_invariant hB
    (eigenspace_invariant_of_commute hAB α))

/--If A and B are commuting symmetric operators acting on a finite dimensional inner product space,
then the simultaneous eigenspaces of A and B exhaust the space. -/
theorem iSup_iSup_eigenspace_inf_eigenspace_eq_top :
    (⨆ (α : 𝕜), (⨆ (γ : 𝕜), (eigenspace A α ⊓ eigenspace B γ))) = ⊤ := by
  have : (fun (α : 𝕜) ↦  eigenspace A α)  = fun (α : 𝕜) ↦
      (⨆ (γ : 𝕜), (eigenspace A α ⊓ eigenspace B γ)) := by
    funext γ
    rw [← eigenspace_restrict_eigenspace_eq_inf hAB, ← Submodule.map_iSup,
      iSup_inf_eq_top hB hAB, Submodule.map_top, Submodule.range_subtype]
  rw [← Submodule.orthogonal_eq_bot_iff.mp (hA.orthogonalComplement_iSup_eigenspaces_eq_bot), this]

/--The simultaneous eigenspaces of a pair of commuting symmetric operators form an
`OrthogonalFamily`.-/
theorem orthogonalFamily_eigenspace_inf_eigenspace :
    OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
    (fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ) := by
  refine orthogonalFamily_iff_pairwise.mpr ?_
  intro i j hij v ⟨hv1 , hv2⟩
  have H:=  (Iff.not (Iff.symm Prod.ext_iff)).mpr hij
  push_neg at H
  by_cases C: i.1 = j.1
  <;> intro w ⟨hw1, hw2⟩
  · exact orthogonalFamily_iff_pairwise.mp hA.orthogonalFamily_eigenspaces (H C) hv1 w hw1
  · exact orthogonalFamily_iff_pairwise.mp hB.orthogonalFamily_eigenspaces C hv2 w hw2

/-- Given a commuting pair of symmetric linear operators on a finite dimensional inner product space
, the space decomposes as an internal direct sum of simultaneous eigenspaces of these operators. -/
theorem DirectSum.IsInternal_of_simultaneous_eigenspaces_of_commuting_symmetric_pair:
    DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)):= by
  apply (OrthogonalFamily.isInternal_iff
    (orthogonalFamily_eigenspace_inf_eigenspace hA hB)).mpr
  rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top hA hB hAB

end Pair

end IsSymmetric

end LinearMap
