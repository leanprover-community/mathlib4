/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton and Samyak Dhar Tuladhar
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum


/-! # Simultaneous eigenspaces of commuting tuples of symmetric operators

This file collects various decomposition results for simultaneous eigenspaces of commuting
tuples of symmetric operators on a finite dimensional Hilbert space.

# Main Results

*

## TODO

Develop `Diagonalization` class that selects a basis of (simultaneous) eigenvectors in a
principled way.

## Tags

self-adjoint operator, simultaneous eigenspaces, simultaneous diagonalization

-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

open Module.End

namespace LinearMap

namespace IsSymmetric

section Pair

variable {α : 𝕜} {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A)

theorem eigenspace_invariant (α : 𝕜) : ∀ v ∈ (eigenspace A α), (B v ∈ eigenspace A α) := by
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
      obtain ⟨_, hy⟩ := h
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

theorem DirectSum.IsInternal_of_simultaneous_eigenspaces_of_commuting_symmetric_pair:
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

end IsSymmetric

end LinearMap
