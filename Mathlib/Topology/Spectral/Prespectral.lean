/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Order.Ideal
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.LocalAtTarget

/-!

# Prespectral spaces

In this file, we define prespectral spaces as spaces whose lattice of compact opens forms a basis.

-/

open TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is prespectral if the lattice of compact opens forms a basis. -/
@[mk_iff]
class PrespectralSpace (X : Type*) [TopologicalSpace X] : Prop where
  isTopologicalBasis : TopologicalSpace.IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U }

/-- A space is prespectral if it has a basis consisting of compact opens. -/
lemma PrespectralSpace.of_isTopologicalBasis {B : Set (Set X)}
    (basis : IsTopologicalBasis B) (isCompact_basis : ∀ U ∈ B, IsCompact U) :
    PrespectralSpace X where
  isTopologicalBasis.exists_subset_inter _ ht₁ _ ht₂ _ hx :=
    have ⟨v, hvB, hv⟩ := basis.exists_subset_of_mem_open hx (ht₁.1.inter ht₂.1)
    ⟨v, ⟨basis.isOpen hvB, isCompact_basis v hvB⟩, hv⟩
  isTopologicalBasis.sUnion_eq := Set.univ_subset_iff.mp (basis.sUnion_eq.superset.trans
    (Set.sUnion_mono fun s hs ↦ ⟨basis.isOpen hs, isCompact_basis s hs⟩))
  isTopologicalBasis.eq_generateFrom := (le_generateFrom fun _ h ↦ h.1).antisymm (le_trans
    (generateFrom_anti fun s hs ↦ ⟨basis.isOpen hs, isCompact_basis s hs⟩) basis.eq_generateFrom.ge)

/-- A variant with an indexed basis instead. -/
lemma PrespectralSpace.of_isTopologicalBasis' {ι : Type*} {b : ι → Set X}
    (basis : IsTopologicalBasis (Set.range b)) (isCompact_basis : ∀ i, IsCompact (b i)) :
    PrespectralSpace X :=
  .of_isTopologicalBasis basis (by aesop)

instance (priority := low) [NoetherianSpace X] : PrespectralSpace X :=
  .of_isTopologicalBasis isTopologicalBasis_opens fun _ _ ↦ NoetherianSpace.isCompact _

instance (priority := low) [PrespectralSpace X] : LocallyCompactSpace X where
  local_compact_nhds _ _ hn :=
    have ⟨V, ⟨hV₁, hV₂⟩, hxV, hVn⟩ := PrespectralSpace.isTopologicalBasis.mem_nhds_iff.mp hn
    ⟨V, hV₁.mem_nhds hxV, hVn, hV₂⟩

open PrespectralSpace in
instance (priority := low) [T2Space X] [PrespectralSpace X] : TotallyDisconnectedSpace X where
  isTotallyDisconnected_univ := isTotallyDisconnected_of_isClopen_set fun _ _ hxy ↦
    have ⟨U, ⟨hU₁, hU₂⟩, hxU, hyU⟩ :=
      isTopologicalBasis.exists_subset_of_mem_open hxy isClosed_singleton.isOpen_compl
    ⟨U, ⟨hU₂.isClosed, hU₁⟩, hxU, fun h ↦ hyU h rfl⟩

lemma PrespectralSpace.of_isOpenCover
    {ι : Type*} {U : ι → Opens X} (hU : IsOpenCover U) [∀ i, PrespectralSpace (U i)] :
    PrespectralSpace X := by
  refine .of_isTopologicalBasis (hU.isTopologicalBasis fun i ↦ isTopologicalBasis) ?_
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_comm (α := Set _), forall_apply_eq_imp_iff₂]
  exact fun i V hV hV' ↦ hV'.image continuous_subtype_val

lemma PrespectralSpace.of_isInducing [PrespectralSpace Y]
    (f : X → Y) (hf : IsInducing f) (hf' : IsSpectralMap f) : PrespectralSpace X :=
  .of_isTopologicalBasis (PrespectralSpace.isTopologicalBasis.isInducing hf) (by
    simp only [Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro _ U h₁ h₂ rfl
    exact hf'.isCompact_preimage_of_isOpen h₁ h₂)

/-- In a prespectral space, the lattice of opens is determined by its lattice of compact opens. -/
def PrespectralSpace.opensEquiv [PrespectralSpace X] :
    Opens X ≃o Order.Ideal (CompactOpens X) where
  toFun U := ⟨⟨{ V | (V : Set X) ⊆ U }, fun U₁ U₂ h₁ h₂ ↦ subset_trans (α := Set X) h₁ h₂⟩,
    ⟨⊥, by simp⟩, fun U₁ h₁ U₂ h₂ ↦ ⟨U₁ ⊔ U₂, by aesop, le_sup_left, le_sup_right⟩⟩
  invFun I := ⨆ U ∈ I, U.toOpens
  left_inv U := by
    apply le_antisymm
    · simp only [Set.mem_setOf_eq, LowerSet.carrier_eq_coe, LowerSet.coe_mk,
        CompactOpens.coe_sup, id_eq, iSup_le_iff]
      exact fun _ ↦ id
    · intro x hxU
      obtain ⟨V, ⟨h₁, h₂⟩, hxV, hVU⟩ := isTopologicalBasis.exists_subset_of_mem_open hxU U.2
      simp only [Opens.mem_iSup, SetLike.mem_coe]
      refine ⟨⟨⟨_, h₂⟩, h₁⟩, hVU, hxV⟩
  right_inv I := by
    ext U
    dsimp
    show U.toOpens ≤ _ ↔ _
    refine ⟨fun H ↦ ?_, fun h ↦ le_iSup₂ (f := fun U (h : U ∈ I) ↦ U.toOpens) U h⟩
    simp only [← SetLike.coe_subset_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk] at H
    obtain ⟨s, hsI, hs, hU⟩ := U.isCompact.elim_finite_subcover_image (fun U _ ↦ U.2) H
    exact I.lower (a := hs.toFinset.sup fun i ↦ i) (by simpa [← SetLike.coe_subset_coe]) (by simpa)
  map_rel_iff' {U V} := by
    show (∀ (W : CompactOpens X), (W : Set X) ⊆ U → (W : Set X) ⊆ V) ↔ U ≤ V
    refine ⟨?_, fun H W ↦ (le_trans · H)⟩
    intro H x hxU
    obtain ⟨W, ⟨h₁, h₂⟩, hxW, hWU⟩ := isTopologicalBasis.exists_subset_of_mem_open hxU U.2
    exact H ⟨⟨W, h₂⟩, h₁⟩ hWU hxW
