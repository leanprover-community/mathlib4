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
  simp_rw [inducing_subtype_val.inducing_iff, inducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← @Filter.comap_comap _ _ _ _ _ f, Function.comp_apply] at h ⊢
  intro a
  -- ⊢ 𝓝 a = comap Subtype.val (comap f (𝓝 (f ↑a)))
  rw [← h, ← inducing_subtype_val.nhds_eq_comap]
  -- 🎉 no goals
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
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.2⟩
#align set.restrict_preimage_open_embedding Set.restrictPreimage_openEmbedding

alias OpenEmbedding.restrictPreimage := Set.restrictPreimage_openEmbedding
#align open_embedding.restrict_preimage OpenEmbedding.restrictPreimage

theorem Set.restrictPreimage_closedEmbedding (s : Set β) (h : ClosedEmbedding f) :
    ClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ inducing_subtype_val.isClosed_preimage _ h.2⟩
#align set.restrict_preimage_closed_embedding Set.restrictPreimage_closedEmbedding

alias ClosedEmbedding.restrictPreimage := Set.restrictPreimage_closedEmbedding
#align closed_embedding.restrict_preimage ClosedEmbedding.restrictPreimage

theorem Set.restrictPreimage_isClosedMap (s : Set β) (H : IsClosedMap f) :
    IsClosedMap (s.restrictPreimage f) := by
  rintro t ⟨u, hu, e⟩
  -- ⊢ IsClosed (restrictPreimage s f '' t)
  refine' ⟨⟨_, (H _ (IsOpen.isClosed_compl hu)).1, _⟩⟩
  -- ⊢ Subtype.val ⁻¹' (f '' uᶜ)ᶜ = (restrictPreimage s f '' t)ᶜ
  rw [← (congr_arg HasCompl.compl e).trans (compl_compl t)]
  -- ⊢ Subtype.val ⁻¹' (f '' uᶜ)ᶜ = (restrictPreimage s f '' (Subtype.val ⁻¹' u)ᶜ)ᶜ
  simp only [Set.preimage_compl, compl_inj_iff]
  -- ⊢ Subtype.val ⁻¹' (f '' uᶜ) = restrictPreimage s f '' (Subtype.val ⁻¹' u)ᶜ
  ext ⟨x, hx⟩
  -- ⊢ { val := x, property := hx } ∈ Subtype.val ⁻¹' (f '' uᶜ) ↔ { val := x, prope …
  suffices (∃ y, y ∉ u ∧ f y = x) ↔ ∃ y, y ∉ u ∧ f y ∈ s ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, fun ⟨a, b, _, c⟩ => ⟨a, b, c⟩⟩
  -- 🎉 no goals
#align set.restrict_preimage_is_closed_map Set.restrictPreimage_isClosedMap

theorem isOpen_iff_inter_of_iSup_eq_top (s : Set β) : IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) := by
  constructor
  -- ⊢ IsOpen s → ∀ (i : ι), IsOpen (s ∩ ↑(U i))
  · exact fun H i => H.inter (U i).2
    -- 🎉 no goals
  · intro H
    -- ⊢ IsOpen s
    have : ⋃ i, (U i : Set β) = Set.univ := by
      convert congr_arg (SetLike.coe) hU
      simp
    rw [← s.inter_univ, ← this, Set.inter_iUnion]
    -- ⊢ IsOpen (⋃ (i : ι), s ∩ ↑(U i))
    exact isOpen_iUnion H
    -- 🎉 no goals
#align is_open_iff_inter_of_supr_eq_top isOpen_iff_inter_of_iSup_eq_top

theorem isOpen_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsOpen s ↔ ∀ i, IsOpen ((↑) ⁻¹' s : Set (U i)) := by
  -- Porting note: rewrote to avoid ´simp´ issues
  rw [isOpen_iff_inter_of_iSup_eq_top hU s]
  -- ⊢ (∀ (i : ι), IsOpen (s ∩ ↑(U i))) ↔ ∀ (i : ι), IsOpen (Subtype.val ⁻¹' s)
  refine forall_congr' fun i => ?_
  -- ⊢ IsOpen (s ∩ ↑(U i)) ↔ IsOpen (Subtype.val ⁻¹' s)
  rw [(U _).2.openEmbedding_subtype_val.open_iff_image_open]
  -- ⊢ IsOpen (s ∩ ↑(U i)) ↔ IsOpen (Subtype.val '' (Subtype.val ⁻¹' s))
  erw [Set.image_preimage_eq_inter_range]
  -- ⊢ IsOpen (s ∩ ↑(U i)) ↔ IsOpen (s ∩ range Subtype.val)
  rw [Subtype.range_coe, Opens.carrier_eq_coe]
  -- 🎉 no goals
#align is_open_iff_coe_preimage_of_supr_eq_top isOpen_iff_coe_preimage_of_iSup_eq_top

theorem isClosed_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsClosed s ↔ ∀ i, IsClosed ((↑) ⁻¹' s : Set (U i)) := by
  simpa using isOpen_iff_coe_preimage_of_iSup_eq_top hU sᶜ
  -- 🎉 no goals
#align is_closed_iff_coe_preimage_of_supr_eq_top isClosed_iff_coe_preimage_of_iSup_eq_top

theorem isClosedMap_iff_isClosedMap_of_iSup_eq_top :
    IsClosedMap f ↔ ∀ i, IsClosedMap ((U i).1.restrictPreimage f) := by
  refine' ⟨fun h i => Set.restrictPreimage_isClosedMap _ h, _⟩
  -- ⊢ (∀ (i : ι), IsClosedMap (restrictPreimage (U i).carrier f)) → IsClosedMap f
  rintro H s hs
  -- ⊢ IsClosed (f '' s)
  rw [isClosed_iff_coe_preimage_of_iSup_eq_top hU]
  -- ⊢ ∀ (i : ι), IsClosed (Subtype.val ⁻¹' (f '' s))
  intro i
  -- ⊢ IsClosed (Subtype.val ⁻¹' (f '' s))
  convert H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  -- ⊢ Subtype.val ⁻¹' (f '' s) = restrictPreimage (U i).carrier f '' (Subtype.val  …
  ext ⟨x, hx⟩
  -- ⊢ { val := x, property := hx } ∈ Subtype.val ⁻¹' (f '' s) ↔ { val := x, proper …
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, fun ⟨a, b, _, c⟩ => ⟨a, b, c⟩⟩
  -- 🎉 no goals
#align is_closed_map_iff_is_closed_map_of_supr_eq_top isClosedMap_iff_isClosedMap_of_iSup_eq_top

theorem inducing_iff_inducing_of_iSup_eq_top (h : Continuous f) :
    Inducing f ↔ ∀ i, Inducing ((U i).1.restrictPreimage f) := by
  simp_rw [inducing_subtype_val.inducing_iff, inducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← @Filter.comap_comap _ _ _ _ _ f]
  constructor
  -- ⊢ (∀ (a : α), 𝓝 a = comap f (𝓝 (f a))) → ∀ (i : ι) (a : ↑(f ⁻¹' (U i).carrier) …
  · intro H i x
    -- ⊢ 𝓝 x = comap Subtype.val (comap f (𝓝 ((f ∘ Subtype.val) x)))
    rw [Function.comp_apply, ← H, ← inducing_subtype_val.nhds_eq_comap]
    -- 🎉 no goals
  · intro H x
    -- ⊢ 𝓝 x = comap f (𝓝 (f x))
    obtain ⟨i, hi⟩ :=
      Opens.mem_iSup.mp
        (show f x ∈ iSup U by
          rw [hU]
          triv)
    erw [← OpenEmbedding.map_nhds_eq (h.1 _ (U i).2).openEmbedding_subtype_val ⟨x, hi⟩]
    -- ⊢ map Subtype.val (𝓝 { val := x, property := hi }) = comap f (𝓝 (f x))
    rw [(H i) ⟨x, hi⟩, Filter.subtype_coe_map_comap, Function.comp_apply, Subtype.coe_mk,
      inf_eq_left, Filter.le_principal_iff]
    exact Filter.preimage_mem_comap ((U i).2.mem_nhds hi)
    -- 🎉 no goals
#align inducing_iff_inducing_of_supr_eq_top inducing_iff_inducing_of_iSup_eq_top

theorem embedding_iff_embedding_of_iSup_eq_top (h : Continuous f) :
    Embedding f ↔ ∀ i, Embedding ((U i).1.restrictPreimage f) := by
  simp_rw [embedding_iff]
  -- ⊢ Inducing f ∧ Function.Injective f ↔ ∀ (i : ι), Inducing (restrictPreimage (U …
  rw [forall_and]
  -- ⊢ Inducing f ∧ Function.Injective f ↔ (∀ (x : ι), Inducing (restrictPreimage ( …
  apply and_congr
  -- ⊢ Inducing f ↔ ∀ (x : ι), Inducing (restrictPreimage (U x).carrier f)
  · apply inducing_iff_inducing_of_iSup_eq_top <;> assumption
    -- ⊢ ⨆ (i : ι), U i = ⊤
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
  · apply Set.injective_iff_injective_of_iUnion_eq_univ
    -- ⊢ ⋃ (i : ι), (U i).carrier = univ
    convert congr_arg SetLike.coe hU
    -- ⊢ ⋃ (i : ι), (U i).carrier = ↑(iSup U)
    simp
    -- 🎉 no goals
#align embedding_iff_embedding_of_supr_eq_top embedding_iff_embedding_of_iSup_eq_top

theorem openEmbedding_iff_openEmbedding_of_iSup_eq_top (h : Continuous f) :
    OpenEmbedding f ↔ ∀ i, OpenEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [openEmbedding_iff]
  -- ⊢ Embedding f ∧ IsOpen (range f) ↔ ∀ (i : ι), Embedding (restrictPreimage (U i …
  rw [forall_and]
  -- ⊢ Embedding f ∧ IsOpen (range f) ↔ (∀ (x : ι), Embedding (restrictPreimage (U  …
  apply and_congr
  -- ⊢ Embedding f ↔ ∀ (x : ι), Embedding (restrictPreimage (U x).carrier f)
  · apply embedding_iff_embedding_of_iSup_eq_top <;> assumption
    -- ⊢ ⨆ (i : ι), U i = ⊤
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
  · simp_rw [Set.range_restrictPreimage]
    -- ⊢ IsOpen (range f) ↔ ∀ (x : ι), IsOpen (Subtype.val ⁻¹' range f)
    apply isOpen_iff_coe_preimage_of_iSup_eq_top hU
    -- 🎉 no goals
#align open_embedding_iff_open_embedding_of_supr_eq_top openEmbedding_iff_openEmbedding_of_iSup_eq_top

theorem closedEmbedding_iff_closedEmbedding_of_iSup_eq_top (h : Continuous f) :
    ClosedEmbedding f ↔ ∀ i, ClosedEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [closedEmbedding_iff]
  -- ⊢ Embedding f ∧ IsClosed (range f) ↔ ∀ (i : ι), Embedding (restrictPreimage (U …
  rw [forall_and]
  -- ⊢ Embedding f ∧ IsClosed (range f) ↔ (∀ (x : ι), Embedding (restrictPreimage ( …
  apply and_congr
  -- ⊢ Embedding f ↔ ∀ (x : ι), Embedding (restrictPreimage (U x).carrier f)
  · apply embedding_iff_embedding_of_iSup_eq_top <;> assumption
    -- ⊢ ⨆ (i : ι), U i = ⊤
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
  · simp_rw [Set.range_restrictPreimage]
    -- ⊢ IsClosed (range f) ↔ ∀ (x : ι), IsClosed (Subtype.val ⁻¹' range f)
    apply isClosed_iff_coe_preimage_of_iSup_eq_top hU
    -- 🎉 no goals
#align closed_embedding_iff_closed_embedding_of_supr_eq_top closedEmbedding_iff_closedEmbedding_of_iSup_eq_top
