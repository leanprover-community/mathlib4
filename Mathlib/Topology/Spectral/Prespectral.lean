/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Order.Ideal
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Spectral.Hom

/-!

# Prespectral spaces

In this file, we define prespectral spaces as spaces whose lattice of compact opens forms a basis.

-/

open TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is prespectral if the lattice of compact opens forms a basis. -/
@[stacks 08YG "The last condition for spectral spaces", mk_iff]
class PrespectralSpace (X : Type*) [TopologicalSpace X] : Prop where
  isTopologicalBasis : IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U }

/-- A space is prespectral if it has a basis consisting of compact opens. -/
lemma PrespectralSpace.of_isTopologicalBasis {B : Set (Set X)}
    (basis : IsTopologicalBasis B) (isCompact_basis : ∀ U ∈ B, IsCompact U) :
    PrespectralSpace X where
  isTopologicalBasis := basis.of_isOpen_of_subset (fun _ h ↦ h.1)
    fun s hs ↦ ⟨basis.isOpen hs, isCompact_basis s hs⟩

/-- A space is prespectral if it has a basis consisting of compact opens.
This is the variant with an indexed basis instead. -/
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
instance (priority := low) [T2Space X] [PrespectralSpace X] : TotallySeparatedSpace X :=
  totallySeparatedSpace_iff_exists_isClopen.mpr fun _ _ hxy ↦
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

lemma PrespectralSpace.of_isClosedEmbedding [PrespectralSpace Y]
    (f : X → Y) (hf : IsClosedEmbedding f) : PrespectralSpace X :=
  .of_isInducing f hf.isInducing hf.isProperMap.isSpectralMap

instance PrespectralSpace.sigma {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    [∀ i, PrespectralSpace (X i)] : PrespectralSpace (Σ i, X i) :=
  .of_isTopologicalBasis (IsTopologicalBasis.sigma fun i ↦ isTopologicalBasis) fun U hU ↦ by
    simp_rw [Set.mem_iUnion] at hU
    obtain ⟨i, V, hV, rfl⟩ := hU
    exact hV.2.image continuous_sigmaMk

variable (X) in
lemma PrespectralSpace.isBasis_opens [PrespectralSpace X] :
    TopologicalSpace.Opens.IsBasis { U : Opens X | IsCompact (U : Set X) } := by
  dsimp only [TopologicalSpace.Opens.IsBasis]
  convert isTopologicalBasis (X := X)
  ext s
  exact ⟨fun ⟨V, hV, heq⟩ ↦ heq ▸ ⟨V.2, hV⟩, fun h ↦ ⟨⟨s, h.1⟩, h.2, rfl⟩⟩

/-- In a prespectral space, the lattice of opens is determined by its lattice of compact opens. -/
def PrespectralSpace.opensEquiv [PrespectralSpace X] :
    Opens X ≃o Order.Ideal (CompactOpens X) where
  toFun U := ⟨⟨{ V | (V : Set X) ⊆ U }, fun U₁ U₂ h₁ h₂ ↦ subset_trans (α := Set X) h₁ h₂⟩,
    ⟨⊥, by simp⟩, fun U₁ h₁ U₂ h₂ ↦ ⟨U₁ ⊔ U₂, by aesop, le_sup_left, le_sup_right⟩⟩
  invFun I := ⨆ U ∈ I, U.toOpens
  left_inv U := by
    apply le_antisymm
    · simp only [iSup_le_iff]
      exact fun _ ↦ id
    · intro x hxU
      obtain ⟨V, ⟨h₁, h₂⟩, hxV, hVU⟩ := isTopologicalBasis.exists_subset_of_mem_open hxU U.2
      simp only [Opens.mem_iSup, SetLike.mem_coe]
      exact ⟨⟨⟨_, h₂⟩, h₁⟩, hVU, hxV⟩
  right_inv I := by
    ext U
    dsimp
    change U.toOpens ≤ _ ↔ _
    refine ⟨fun H ↦ ?_, fun h ↦ le_iSup₂ (f := fun U (h : U ∈ I) ↦ U.toOpens) U h⟩
    simp only [← SetLike.coe_subset_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk] at H
    obtain ⟨s, hsI, hs, hU⟩ := U.isCompact.elim_finite_subcover_image (fun U _ ↦ U.2) H
    exact I.lower (a := hs.toFinset.sup fun i ↦ i) (by simpa [← SetLike.coe_subset_coe]) (by simpa)
  map_rel_iff' {U V} := by
    change (∀ (W : CompactOpens X), (W : Set X) ⊆ U → (W : Set X) ⊆ V) ↔ U ≤ V
    refine ⟨?_, fun H W ↦ (le_trans · H)⟩
    intro H x hxU
    obtain ⟨W, ⟨h₁, h₂⟩, hxW, hWU⟩ := isTopologicalBasis.exists_subset_of_mem_open hxU U.2
    exact H ⟨⟨W, h₂⟩, h₁⟩ hWU hxW

open TopologicalSpace Opens in
/-- If `X` has a basis of compact opens and `f : X → S` is open, every
compact open of `S` is the image of a compact open of `X`. -/
lemma IsOpenMap.exists_opens_image_eq_of_prespectralSpace [PrespectralSpace X] {f : X → Y}
    (hfc : Continuous f) (h : IsOpenMap f) {U : Set Y} (hs : U ⊆ Set.range f) (hU : IsOpen U)
    (hc : IsCompact U) : ∃ (V : Opens X), IsCompact V.1 ∧ f '' V = U := by
  obtain ⟨Us, hUs, heq⟩ := TopologicalSpace.Opens.isBasis_iff_cover.mp
    (PrespectralSpace.isBasis_opens X) ⟨f ⁻¹' U, hU.preimage hfc⟩
  obtain ⟨t, ht⟩ := by
    refine hc.elim_finite_subcover (fun s : Us ↦ f '' s.1) (fun s ↦ h _ s.1.2) (fun x hx ↦ ?_)
    obtain ⟨x, rfl⟩ := hs hx
    obtain ⟨i, hi, hx⟩ := mem_sSup.mp <| by rwa [← heq]
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, x, hx, rfl⟩
  refine ⟨⨆ s ∈ t, s.1, ?_, ?_⟩
  · simp only [iSup_mk, carrier_eq_coe, coe_mk]
    exact t.finite_toSet.isCompact_biUnion fun i _ ↦ hUs i.2
  · simp only [iSup_mk, carrier_eq_coe, Set.iUnion_coe_set, coe_mk, Set.image_iUnion]
    convert_to ⋃ i ∈ t, f '' i.1 = U
    · simp
    · refine subset_antisymm (fun x ↦ ?_) ht
      simp_rw [Set.mem_iUnion]
      rintro ⟨i, hi, x, hx, rfl⟩
      have := heq ▸ mem_sSup.mpr ⟨i.1, i.2, hx⟩
      exact this
