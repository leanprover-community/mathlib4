/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Sets.Opens

#align_import topology.local_at_target from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Properties of maps that are local at the target.

We show that the following properties of continuous maps are local at the target :
- `Inducing`
- `Embedding`
- `OpenEmbedding`
- `ClosedEmbedding`

-/


open TopologicalSpace Set Filter

open Topology Filter

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
variable {s : Set β} {ι : Type*} {U : ι → Opens β} (hU : iSup U = ⊤)

theorem Set.restrictPreimage_inducing (s : Set β) (h : Inducing f) :
    Inducing (s.restrictPreimage f) := by
  simp_rw [← inducing_subtype_val.of_comp_iff, inducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← @Filter.comap_comap _ _ _ _ _ f, Function.comp_apply] at h ⊢
  intro a
  rw [← h, ← inducing_subtype_val.nhds_eq_comap]
#align set.restrict_preimage_inducing Set.restrictPreimage_inducing

alias Inducing.restrictPreimage := Set.restrictPreimage_inducing
#align inducing.restrict_preimage Inducing.restrictPreimage

theorem Set.restrictPreimage_embedding (s : Set β) (h : Embedding f) :
    Embedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩
#align set.restrict_preimage_embedding Set.restrictPreimage_embedding

alias Embedding.restrictPreimage := Set.restrictPreimage_embedding
#align embedding.restrict_preimage Embedding.restrictPreimage

theorem Set.restrictPreimage_openEmbedding (s : Set β) (h : OpenEmbedding f) :
    OpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.isOpen_range⟩
#align set.restrict_preimage_open_embedding Set.restrictPreimage_openEmbedding

alias OpenEmbedding.restrictPreimage := Set.restrictPreimage_openEmbedding
#align open_embedding.restrict_preimage OpenEmbedding.restrictPreimage

theorem Set.restrictPreimage_closedEmbedding (s : Set β) (h : ClosedEmbedding f) :
    ClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ inducing_subtype_val.isClosed_preimage _ h.isClosed_range⟩
#align set.restrict_preimage_closed_embedding Set.restrictPreimage_closedEmbedding

alias ClosedEmbedding.restrictPreimage := Set.restrictPreimage_closedEmbedding
#align closed_embedding.restrict_preimage ClosedEmbedding.restrictPreimage

theorem IsClosedMap.restrictPreimage (H : IsClosedMap f) (s : Set β) :
    IsClosedMap (s.restrictPreimage f) := by
  intro t
  suffices ∀ u, IsClosed u → Subtype.val ⁻¹' u = t →
    ∃ v, IsClosed v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isClosed_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

@[deprecated] -- since 2024-04-02
theorem Set.restrictPreimage_isClosedMap (s : Set β) (H : IsClosedMap f) :
    IsClosedMap (s.restrictPreimage f) := H.restrictPreimage s

theorem IsOpenMap.restrictPreimage (H : IsOpenMap f) (s : Set β) :
    IsOpenMap (s.restrictPreimage f) := by
  intro t
  suffices ∀ u, IsOpen u → Subtype.val ⁻¹' u = t →
    ∃ v, IsOpen v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isOpen_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

@[deprecated] -- since 2024-04-02
theorem Set.restrictPreimage_isOpenMap (s : Set β) (H : IsOpenMap f) :
    IsOpenMap (s.restrictPreimage f) := H.restrictPreimage s

theorem isOpen_iff_inter_of_iSup_eq_top (s : Set β) : IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) := by
  constructor
  · exact fun H i => H.inter (U i).2
  · intro H
    have : ⋃ i, (U i : Set β) = Set.univ := by
      convert congr_arg (SetLike.coe) hU
      simp
    rw [← s.inter_univ, ← this, Set.inter_iUnion]
    exact isOpen_iUnion H
#align is_open_iff_inter_of_supr_eq_top isOpen_iff_inter_of_iSup_eq_top

theorem isOpen_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsOpen s ↔ ∀ i, IsOpen ((↑) ⁻¹' s : Set (U i)) := by
  -- Porting note: rewrote to avoid ´simp´ issues
  rw [isOpen_iff_inter_of_iSup_eq_top hU s]
  refine forall_congr' fun i => ?_
  rw [(U _).2.openEmbedding_subtype_val.open_iff_image_open]
  erw [Set.image_preimage_eq_inter_range]
  rw [Subtype.range_coe, Opens.carrier_eq_coe]
#align is_open_iff_coe_preimage_of_supr_eq_top isOpen_iff_coe_preimage_of_iSup_eq_top

theorem isClosed_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsClosed s ↔ ∀ i, IsClosed ((↑) ⁻¹' s : Set (U i)) := by
  simpa using isOpen_iff_coe_preimage_of_iSup_eq_top hU sᶜ
#align is_closed_iff_coe_preimage_of_supr_eq_top isClosed_iff_coe_preimage_of_iSup_eq_top

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
#align is_closed_map_iff_is_closed_map_of_supr_eq_top isClosedMap_iff_isClosedMap_of_iSup_eq_top

theorem inducing_iff_inducing_of_iSup_eq_top (h : Continuous f) :
    Inducing f ↔ ∀ i, Inducing ((U i).1.restrictPreimage f) := by
  simp_rw [← inducing_subtype_val.of_comp_iff, inducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← @Filter.comap_comap _ _ _ _ _ f]
  constructor
  · intro H i x
    rw [Function.comp_apply, ← H, ← inducing_subtype_val.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ :=
      Opens.mem_iSup.mp
        (show f x ∈ iSup U by
          rw [hU]
          trivial)
    erw [← OpenEmbedding.map_nhds_eq (h.1 _ (U i).2).openEmbedding_subtype_val ⟨x, hi⟩]
    rw [(H i) ⟨x, hi⟩, Filter.subtype_coe_map_comap, Function.comp_apply, Subtype.coe_mk,
      inf_eq_left, Filter.le_principal_iff]
    exact Filter.preimage_mem_comap ((U i).2.mem_nhds hi)
#align inducing_iff_inducing_of_supr_eq_top inducing_iff_inducing_of_iSup_eq_top

theorem embedding_iff_embedding_of_iSup_eq_top (h : Continuous f) :
    Embedding f ↔ ∀ i, Embedding ((U i).1.restrictPreimage f) := by
  simp_rw [embedding_iff]
  rw [forall_and]
  apply and_congr
  · apply inducing_iff_inducing_of_iSup_eq_top <;> assumption
  · apply Set.injective_iff_injective_of_iUnion_eq_univ
    convert congr_arg SetLike.coe hU
    simp
#align embedding_iff_embedding_of_supr_eq_top embedding_iff_embedding_of_iSup_eq_top

theorem openEmbedding_iff_openEmbedding_of_iSup_eq_top (h : Continuous f) :
    OpenEmbedding f ↔ ∀ i, OpenEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [openEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply embedding_iff_embedding_of_iSup_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply isOpen_iff_coe_preimage_of_iSup_eq_top hU
#align open_embedding_iff_open_embedding_of_supr_eq_top openEmbedding_iff_openEmbedding_of_iSup_eq_top

theorem closedEmbedding_iff_closedEmbedding_of_iSup_eq_top (h : Continuous f) :
    ClosedEmbedding f ↔ ∀ i, ClosedEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [closedEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply embedding_iff_embedding_of_iSup_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply isClosed_iff_coe_preimage_of_iSup_eq_top hU
#align closed_embedding_iff_closed_embedding_of_supr_eq_top closedEmbedding_iff_closedEmbedding_of_iSup_eq_top
