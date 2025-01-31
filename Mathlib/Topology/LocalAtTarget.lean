/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.LocallyClosed

/-!
# Properties of maps that are local at the target.

We show that the following properties of continuous maps are local at the target :
- `IsInducing`
- `IsEmbedding`
- `IsOpenEmbedding`
- `IsClosedEmbedding`

-/

open Filter Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
variable {ι : Type*} {U : ι → Opens β}

theorem Set.restrictPreimage_isInducing (s : Set β) (h : IsInducing f) :
    IsInducing (s.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← @Filter.comap_comap _ _ _ _ _ f, Function.comp_apply] at h ⊢
  intro a
  rw [← h, ← IsInducing.subtypeVal.nhds_eq_comap]

@[deprecated (since := "2024-10-28")]
alias Set.restrictPreimage_inducing := Set.restrictPreimage_isInducing

alias Topology.IsInducing.restrictPreimage := Set.restrictPreimage_isInducing

@[deprecated (since := "2024-10-28")] alias Inducing.restrictPreimage := IsInducing.restrictPreimage

theorem Set.restrictPreimage_isEmbedding (s : Set β) (h : IsEmbedding f) :
    IsEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩

@[deprecated (since := "2024-10-26")]
alias Set.restrictPreimage_embedding := Set.restrictPreimage_isEmbedding

alias Topology.IsEmbedding.restrictPreimage := Set.restrictPreimage_isEmbedding

@[deprecated (since := "2024-10-26")]
alias Embedding.restrictPreimage := IsEmbedding.restrictPreimage

theorem Set.restrictPreimage_isOpenEmbedding (s : Set β) (h : IsOpenEmbedding f) :
    IsOpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.isOpen_range⟩

@[deprecated (since := "2024-10-18")]
alias Set.restrictPreimage_openEmbedding := Set.restrictPreimage_isOpenEmbedding

alias Topology.IsOpenEmbedding.restrictPreimage := Set.restrictPreimage_isOpenEmbedding

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.restrictPreimage := IsOpenEmbedding.restrictPreimage

theorem Set.restrictPreimage_isClosedEmbedding (s : Set β) (h : IsClosedEmbedding f) :
    IsClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ IsInducing.subtypeVal.isClosed_preimage _ h.isClosed_range⟩

@[deprecated (since := "2024-10-20")]
alias Set.restrictPreimage_closedEmbedding := Set.restrictPreimage_isClosedEmbedding

alias Topology.IsClosedEmbedding.restrictPreimage := Set.restrictPreimage_isClosedEmbedding

@[deprecated (since := "2024-10-20")]
alias ClosedEmbedding.restrictPreimage := IsClosedEmbedding.restrictPreimage

theorem IsClosedMap.restrictPreimage (H : IsClosedMap f) (s : Set β) :
    IsClosedMap (s.restrictPreimage f) := by
  intro t
  suffices ∀ u, IsClosed u → Subtype.val ⁻¹' u = t →
    ∃ v, IsClosed v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isClosed_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

theorem IsOpenMap.restrictPreimage (H : IsOpenMap f) (s : Set β) :
    IsOpenMap (s.restrictPreimage f) := by
  intro t
  suffices ∀ u, IsOpen u → Subtype.val ⁻¹' u = t →
    ∃ v, IsOpen v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isOpen_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

variable (hU : iSup U = ⊤)
include hU

theorem isOpen_iff_inter_of_iSup_eq_top (s : Set β) : IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) := by
  constructor
  · exact fun H i => H.inter (U i).2
  · intro H
    have : ⋃ i, (U i : Set β) = Set.univ := by
      convert congr_arg (SetLike.coe) hU
      simp
    rw [← s.inter_univ, ← this, Set.inter_iUnion]
    exact isOpen_iUnion H

theorem isOpen_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsOpen s ↔ ∀ i, IsOpen ((↑) ⁻¹' s : Set (U i)) := by
  simp [isOpen_iff_inter_of_iSup_eq_top hU s,
    (U _).2.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
    Set.image_preimage_eq_inter_range]

theorem isClosed_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsClosed s ↔ ∀ i, IsClosed ((↑) ⁻¹' s : Set (U i)) := by
  simpa using isOpen_iff_coe_preimage_of_iSup_eq_top hU sᶜ

theorem isLocallyClosed_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsLocallyClosed s ↔ ∀ i, IsLocallyClosed ((↑) ⁻¹' s : Set (U i)) := by
  simp_rw [isLocallyClosed_iff_isOpen_coborder]
  rw [isOpen_iff_coe_preimage_of_iSup_eq_top hU]
  exact forall_congr' fun i ↦ by
    have : coborder ((↑) ⁻¹' s : Set (U i)) = Subtype.val ⁻¹' coborder s := by
      exact (U i).isOpen.isOpenEmbedding_subtypeVal.coborder_preimage _
    rw [this]

theorem isOpenMap_iff_isOpenMap_of_iSup_eq_top :
    IsOpenMap f ↔ ∀ i, IsOpenMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, ?_⟩
  rintro H s hs
  rw [isOpen_iff_coe_preimage_of_iSup_eq_top hU]
  intro i
  convert H i _ (hs.preimage continuous_subtype_val)
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, fun ⟨a, b, _, c⟩ => ⟨a, b, c⟩⟩

theorem isClosedMap_iff_isClosedMap_of_iSup_eq_top :
    IsClosedMap f ↔ ∀ i, IsClosedMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, ?_⟩
  rintro H s hs
  rw [isClosed_iff_coe_preimage_of_iSup_eq_top hU]
  intro i
  convert H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, fun ⟨a, b, _, c⟩ => ⟨a, b, c⟩⟩

theorem inducing_iff_inducing_of_iSup_eq_top (h : Continuous f) :
    IsInducing f ↔ ∀ i, IsInducing ((U i).1.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← @Filter.comap_comap _ _ _ _ _ f]
  constructor
  · intro H i x
    rw [Function.comp_apply, ← H, ← IsInducing.subtypeVal.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ :=
      Opens.mem_iSup.mp
        (show f x ∈ iSup U by
          rw [hU]
          trivial)
    rw [← IsOpenEmbedding.map_nhds_eq (h.1 _ (U i).2).isOpenEmbedding_subtypeVal ⟨x, hi⟩,
      (H i) ⟨x, hi⟩, Filter.subtype_coe_map_comap, Function.comp_apply, Subtype.coe_mk,
      inf_eq_left, Filter.le_principal_iff]
    exact Filter.preimage_mem_comap ((U i).2.mem_nhds hi)

theorem isEmbedding_iff_of_iSup_eq_top (h : Continuous f) :
    IsEmbedding f ↔ ∀ i, IsEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply inducing_iff_inducing_of_iSup_eq_top <;> assumption
  · apply Set.injective_iff_injective_of_iUnion_eq_univ
    convert congr_arg SetLike.coe hU
    simp

omit hU in
/--
Given a continuous map `f : X → Y` between topological spaces.
Suppose we have an open cover `V i` of the range of `f`, and an open cover `U i` of `X` that is
coarser than the pullback of `V` under `f`.
To check that `f` is an embedding it suffices to check that `U i → Y` is an embedding for all `i`.
-/
theorem isEmbedding_of_iSup_eq_top_of_preimage_subset_range
    {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : Continuous f) {ι : Type*}
    (U : ι → Opens Y) (hU : Set.range f ⊆ (iSup U :))
    (V : ι → Type*) [∀ i, TopologicalSpace (V i)]
    (iV : ∀ i, V i → X) (hiV : ∀ i, Continuous (iV i)) (hV : ∀ i, f ⁻¹' U i ⊆ Set.range (iV i))
    (hV' : ∀ i, IsEmbedding (f ∘ iV i)) : IsEmbedding f := by
  wlog hU' : iSup U = ⊤
  · let f₀ : X → Set.range f := fun x ↦ ⟨f x, ⟨x, rfl⟩⟩
    suffices IsEmbedding f₀ from IsEmbedding.subtypeVal.comp this
    have hU'' : (⨆ i, (U i).comap ⟨Subtype.val, continuous_subtype_val⟩ :
        Opens (Set.range f)) = ⊤ := by
      rw [← top_le_iff]
      simpa [Set.range_subset_iff, SetLike.le_def] using hU
    refine this _ ?_ _ ?_ V iV hiV ?_ ?_ hU''
    · fun_prop
    · rw [hU'']; simp
    · exact hV
    · exact fun i ↦ IsEmbedding.of_comp (by fun_prop) continuous_subtype_val (hV' i)
  rw [isEmbedding_iff_of_iSup_eq_top hU' h]
  intro i
  let f' := (Subtype.val ∘ (f ⁻¹' U i).restrictPreimage (iV i))
  have : IsEmbedding f' :=
    IsEmbedding.subtypeVal.comp ((IsEmbedding.of_comp (hiV i) h (hV' _)).restrictPreimage _)
  have hf' : Set.range f' = f ⁻¹' U i := by
    simpa [f', Set.range_comp, Set.range_restrictPreimage] using hV i
  let e := (Homeomorph.ofIsEmbedding _ this).trans (Homeomorph.setCongr hf')
  refine IsEmbedding.of_comp (by fun_prop) continuous_subtype_val ?_
  convert ((hV' i).comp IsEmbedding.subtypeVal).comp e.symm.isEmbedding
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp
  rfl

@[deprecated (since := "2024-10-26")]
alias embedding_iff_embedding_of_iSup_eq_top := isEmbedding_iff_of_iSup_eq_top

theorem isOpenEmbedding_iff_isOpenEmbedding_of_iSup_eq_top (h : Continuous f) :
    IsOpenEmbedding f ↔ ∀ i, IsOpenEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isOpenEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply isEmbedding_iff_of_iSup_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply isOpen_iff_coe_preimage_of_iSup_eq_top hU

@[deprecated (since := "2024-10-18")]
alias openEmbedding_iff_openEmbedding_of_iSup_eq_top :=
  isOpenEmbedding_iff_isOpenEmbedding_of_iSup_eq_top

theorem isClosedEmbedding_iff_isClosedEmbedding_of_iSup_eq_top (h : Continuous f) :
    IsClosedEmbedding f ↔ ∀ i, IsClosedEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isClosedEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply isEmbedding_iff_of_iSup_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply isClosed_iff_coe_preimage_of_iSup_eq_top hU

omit [TopologicalSpace α] in
theorem denseRange_iff_denseRange_of_iSup_eq_top :
    DenseRange f ↔ ∀ i, DenseRange ((U i).1.restrictPreimage f) := by
  simp_rw [denseRange_iff_closure_range, Set.range_restrictPreimage,
    ← (U _).2.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
  simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe, preimage_eq_univ_iff,
    Subtype.range_coe_subtype, SetLike.mem_coe]
  rw [← iUnion_subset_iff, ← Set.univ_subset_iff, iff_iff_eq]
  congr 1
  simpa using congr(($hU).1).symm

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_iff_closedEmbedding_of_iSup_eq_top :=
 isClosedEmbedding_iff_isClosedEmbedding_of_iSup_eq_top
