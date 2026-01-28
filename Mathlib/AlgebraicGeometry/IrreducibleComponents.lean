/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Lasker

/-!
# Irreducible Components of Noetherian Schemes

-/

@[expose] public section

namespace AlgebraicGeometry.Scheme

theorem sUnion_irreducibleComponents {α : Type*} [TopologicalSpace α] :
    ⋃₀ irreducibleComponents α = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ Set.mem_sUnion_of_mem mem_irreducibleComponent
    (irreducibleComponent_mem_irreducibleComponents x)

theorem not_subset_sUnion_of_subset_irreducibleComponents {α : Type*} [TopologicalSpace α]
    (Z : Set α) (hZ : Z ∈ irreducibleComponents α) (S : Set (Set α)) (hS : S.Finite)
    (hSα : S ⊆ irreducibleComponents α) (hZS : Z ∉ S) :
    ¬ Z ⊆ ⋃₀ S := by
  contrapose! hZS
  obtain ⟨W, hWS, hZW⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1 hS.toFinset
    (fun W hW ↦ isClosed_of_mem_irreducibleComponents W (hSα (hS.mem_toFinset.mp hW)))
    (hS.coe_toFinset.symm ▸ hZS)
  rw [hS.mem_toFinset] at hWS
  rwa [Set.Subset.antisymm hZW (hZ.2 (hSα hWS).1 hZW)]

theorem closure_sUnion_irreducibleComponents_diff_singleton
    {α : Type*} [TopologicalSpace α] (hα : (irreducibleComponents α).Finite)
    (Z : Set α) (hZ : Z ∈ irreducibleComponents α) :
    closure (⋃₀ (irreducibleComponents α \ {Z}))ᶜ = Z := by
  have h : (⋃₀ (irreducibleComponents α \ {Z}))ᶜ ⊆ Z := by
    rw [Set.compl_subset_iff_union, ← Set.sUnion_singleton Z, ← Set.sUnion_union,
      Set.sUnion_singleton, Set.diff_union_of_subset, sUnion_irreducibleComponents]
    rwa [Set.singleton_subset_iff]
  refine Set.Subset.antisymm ?_ ?_
  · rwa [IsClosed.closure_subset_iff (isClosed_of_mem_irreducibleComponents Z hZ)]
  · rw [← Set.inter_eq_right.mpr h]
    apply subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2
    · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hα.diff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
    · rw [Set.inter_compl_nonempty_iff]
      exact not_subset_sUnion_of_subset_irreducibleComponents Z hZ _ hα.diff Set.diff_subset
        (Set.notMem_diff_of_mem (Set.mem_singleton Z))

variable (X : Scheme) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) [IsNoetherian X]

def irreducibleComponentIdeal : X.IdealSheafData where
  __ :=
    have hα : (irreducibleComponents X).Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (Opens.ι ⟨(⋃₀ (irreducibleComponents X \ {Z}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hα.diff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩).ker
  supportSet := Z
  supportSet_eq_iInter_zeroLocus := by
    classical
    have hα : (irreducibleComponents X).Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    set Z' : X.Opens := ⟨(⋃₀ (irreducibleComponents X \ {Z}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hα.diff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩
    have h₁ : (Z' : Set X) = (⋃₀ (irreducibleComponents X \ {Z}))ᶜ := by simp [Z']
    have h₂ : closure (Z' : Set X) = Z :=
      closure_sUnion_irreducibleComponents_diff_singleton hα Z hZ
    rw [← IdealSheafData.coe_support_eq_eq_iInter_zeroLocus, Hom.support_ker]
    simpa [Z'] using h₂.symm

noncomputable def irreducibleComponent : Scheme :=
  (X.irreducibleComponentIdeal Z hZ).subscheme

-- todo: prove that in the affine case, this agrees with the second primary

end AlgebraicGeometry.Scheme
