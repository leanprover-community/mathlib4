/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Properties of maps that are local at the target or at the source.

We show that the following properties of continuous maps are local at the target :
- `IsInducing`
- `IsOpenMap`
- `IsClosedMap`
- `IsEmbedding`
- `IsOpenEmbedding`
- `IsClosedEmbedding`
- `GeneralizingMap`

We show that the following properties of continuous maps are local at the source:
- `IsOpenMap`
- `GeneralizingMap`

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

alias Topology.IsInducing.restrictPreimage := Set.restrictPreimage_isInducing

theorem Set.restrictPreimage_isEmbedding (s : Set β) (h : IsEmbedding f) :
    IsEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩

alias Topology.IsEmbedding.restrictPreimage := Set.restrictPreimage_isEmbedding

theorem Set.restrictPreimage_isOpenEmbedding (s : Set β) (h : IsOpenEmbedding f) :
    IsOpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.isOpen_range⟩

alias Topology.IsOpenEmbedding.restrictPreimage := Set.restrictPreimage_isOpenEmbedding

theorem Set.restrictPreimage_isClosedEmbedding (s : Set β) (h : IsClosedEmbedding f) :
    IsClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ IsInducing.subtypeVal.isClosed_preimage _ h.isClosed_range⟩

alias Topology.IsClosedEmbedding.restrictPreimage := Set.restrictPreimage_isClosedEmbedding

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

lemma GeneralizingMap.restrictPreimage (H : GeneralizingMap f) (s : Set β) :
    GeneralizingMap (s.restrictPreimage f) := by
  intro x y h
  obtain ⟨a, ha, hy⟩ := H (h.map <| continuous_subtype_val (p := s))
  use ⟨a, by simp [hy]⟩
  simp [hy, subtype_specializes_iff, ha]

lemma IsProperMap.restrictPreimage (H : IsProperMap f) (s : Set β) :
    IsProperMap (s.restrictPreimage f) := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨H.continuous.restrictPreimage, H.isClosedMap.restrictPreimage _, fun y ↦ ?_⟩
  rw [IsEmbedding.subtypeVal.isCompact_iff, image_val_preimage_restrictPreimage, image_singleton]
  exact H.isCompact_preimage isCompact_singleton

namespace TopologicalSpace.IsOpenCover

section LocalAtTarget

variable {U : ι → Opens β} {s : Set β} (hU : IsOpenCover U)
include hU

theorem isOpen_iff_inter :
    IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) := by
  constructor
  · exact fun H i ↦ H.inter (U i).isOpen
  · intro H
    simpa [← inter_iUnion, hU.iSup_set_eq_univ] using isOpen_iUnion H

theorem isOpen_iff_coe_preimage :
    IsOpen s ↔ ∀ i, IsOpen ((↑) ⁻¹' s : Set (U i)) := by
  simp [hU.isOpen_iff_inter (s := s), (U _).2.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
    image_preimage_eq_inter_range]

theorem isClosed_iff_coe_preimage {s : Set β} :
    IsClosed s ↔ ∀ i, IsClosed ((↑) ⁻¹' s : Set (U i)) := by
  simpa using hU.isOpen_iff_coe_preimage (s := sᶜ)

theorem isLocallyClosed_iff_coe_preimage {s : Set β} :
    IsLocallyClosed s ↔ ∀ i, IsLocallyClosed ((↑) ⁻¹' s : Set (U i)) := by
  have (i : _) : coborder ((↑) ⁻¹' s : Set (U i)) = Subtype.val ⁻¹' coborder s :=
    (U i).isOpen.isOpenEmbedding_subtypeVal.coborder_preimage _
  simp [isLocallyClosed_iff_isOpen_coborder, hU.isOpen_iff_coe_preimage, this]

theorem isOpenMap_iff_restrictPreimage :
    IsOpenMap f ↔ ∀ i, IsOpenMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i ↦ h.restrictPreimage _, fun H s hs ↦ ?_⟩
  rw [hU.isOpen_iff_coe_preimage]
  intro i
  convert H i _ (hs.preimage continuous_subtype_val)
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ ↦ ⟨a, b, c.symm ▸ hx, c⟩, by tauto⟩

theorem isClosedMap_iff_restrictPreimage :
    IsClosedMap f ↔ ∀ i, IsClosedMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, fun H s hs ↦ ?_⟩
  rw [hU.isClosed_iff_coe_preimage]
  intro i
  convert H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, by tauto⟩

theorem isInducing_iff_restrictPreimage (h : Continuous f) :
    IsInducing f ↔ ∀ i, IsInducing ((U i).1.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← Filter.comap_comap]
  constructor
  · intro H i x
    rw [Function.comp_apply, ← H, ← IsInducing.subtypeVal.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show f x ∈ iSup U by simp [hU.iSup_eq_top])
    simpa [← ((h.1 _ (U i).2).isOpenEmbedding_subtypeVal).map_nhds_eq ⟨x, hi⟩, H i ⟨x, hi⟩,
      subtype_coe_map_comap] using preimage_mem_comap ((U i).2.mem_nhds hi)

theorem isEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsEmbedding f ↔ ∀ i, IsEmbedding ((U i).1.restrictPreimage f) := by
  simpa [isEmbedding_iff, forall_and] using and_congr (hU.isInducing_iff_restrictPreimage h)
    (injective_iff_injective_of_iUnion_eq_univ hU.iSup_set_eq_univ)

theorem isOpenEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsOpenEmbedding f ↔ ∀ i, IsOpenEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isOpenEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isOpen_iff_coe_preimage

theorem isClosedEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsClosedEmbedding f ↔ ∀ i, IsClosedEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isClosedEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isClosed_iff_coe_preimage

theorem isHomeomorph_iff_restrictPreimage (h : Continuous f) :
    IsHomeomorph f ↔ ∀ i, IsHomeomorph ((U i).1.restrictPreimage f) := by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective, forall_and,
    ← isEmbedding_iff_restrictPreimage hU h,
    surjective_iff_surjective_of_iUnion_eq_univ hU.iSup_set_eq_univ]
  rfl

omit [TopologicalSpace α] in
theorem denseRange_iff_restrictPreimage :
    DenseRange f ↔ ∀ i, DenseRange ((U i).1.restrictPreimage f) := by
  simp_rw [denseRange_iff_closure_range, Set.range_restrictPreimage,
    ← (U _).2.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
  simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe, preimage_eq_univ_iff,
    Subtype.range_coe_subtype, SetLike.mem_coe]
  rw [← iUnion_subset_iff, ← Set.univ_subset_iff, iff_iff_eq]
  congr 1
  exact hU.iSup_set_eq_univ.symm

lemma generalizingMap_iff_restrictPreimage :
    GeneralizingMap f ↔ ∀ i, GeneralizingMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun hf ↦ fun i ↦ hf.restrictPreimage _, fun hf ↦ fun x y h ↦ ?_⟩
  obtain ⟨i, hx⟩ := hU.exists_mem (f x)
  have h : (⟨y, (U i).2.stableUnderGeneralization h hx⟩ : U i) ⤳
    (U i).1.restrictPreimage f ⟨x, hx⟩ := by rwa [subtype_specializes_iff]
  obtain ⟨a, ha, heq⟩ := hf i h
  refine ⟨a, ?_, congr(($heq).val)⟩
  rwa [subtype_specializes_iff] at ha

end LocalAtTarget

section LocalAtSource

variable {U : ι → Opens α} (hU : IsOpenCover U)
include hU

lemma isOpenMap_iff_comp : IsOpenMap f ↔ ∀ i, IsOpenMap (f ∘ ((↑) : U i → α)) := by
  refine ⟨fun hf ↦ fun i ↦ hf.comp (U i).isOpenEmbedding'.isOpenMap, fun hf ↦ ?_⟩
  intro V hV
  convert isOpen_iUnion (fun i ↦ hf i _ <| isOpen_induced hV)
  simp_rw [Set.image_comp, Set.image_preimage_eq_inter_range, ← Set.image_iUnion,
    Subtype.range_coe_subtype, SetLike.setOf_mem_eq, hU.iUnion_inter]

lemma generalizingMap_iff_comp :
    GeneralizingMap f ↔ ∀ i, GeneralizingMap (f ∘ ((↑) : U i → α)) := by
  refine ⟨fun hf ↦ fun i ↦
      ((U i).isOpenEmbedding'.generalizingMap
        (U i).isOpenEmbedding'.isOpen_range.stableUnderGeneralization).comp hf,
    fun hf ↦ fun x y h ↦ ?_⟩
  obtain ⟨i, hi⟩ := hU.exists_mem x
  replace h : y ⤳ (f ∘ ((↑) : U i → α)) ⟨x, hi⟩ := h
  obtain ⟨a, ha, rfl⟩ := hf i h
  use a.val
  simp [ha.map (U i).isOpenEmbedding'.continuous]

end LocalAtSource

end TopologicalSpace.IsOpenCover


/--
Given a continuous map `f : X → Y` between topological spaces.
Suppose we have an open cover `U i` of the range of `f`, and a family of continuous maps `V i → X`
whose images are a cover of `X` that is coarser than the pullback of `U` under `f`.
To check that `f` is an embedding it suffices to check that `V i → Y` is an embedding for all `i`.
-/
-- TODO : the lemma name does not match the content (there is no hypothesis `iSup_eq_top`!)
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
  rw [(IsOpenCover.mk hU').isEmbedding_iff_restrictPreimage h]
  intro i
  let f' := (Subtype.val ∘ (f ⁻¹' U i).restrictPreimage (iV i))
  have : IsEmbedding f' :=
    IsEmbedding.subtypeVal.comp ((IsEmbedding.of_comp (hiV i) h (hV' _)).restrictPreimage _)
  have hf' : Set.range f' = f ⁻¹' U i := by
    simpa [f', Set.range_comp, Set.range_restrictPreimage] using hV i
  let e := this.toHomeomorph.trans (Homeomorph.setCongr hf')
  refine IsEmbedding.of_comp (by fun_prop) continuous_subtype_val ?_
  convert ((hV' i).comp IsEmbedding.subtypeVal).comp e.symm.isEmbedding
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp
  rfl
