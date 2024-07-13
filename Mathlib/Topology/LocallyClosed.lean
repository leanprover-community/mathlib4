/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.LocalAtTarget

/-!
# Locally closed sets

## Main results
- `IsLocallyClosed`: Predicate saying that a set is locally closed
- `isLocallyClosed_tfae`:
  A set `s` is locally closed if one of the equivalent conditions below hold
  1. It is the intersection of some open set and some closed set.
  2. The coborder `(closure s \ s)ᶜ` is open.
  3. `s` is closed in some neighborhood of `x` for all `x ∈ s`.
  4. Every `x ∈ s` has some open neighborhood `U` such that `U ∩ closure s ⊆ s`.
  5. `s` is open in the closure of `s`.

-/

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {s t : Set α} {f : α → β}

open scoped Topology Set.Notation

/--
The coborder is defined as the complement of `closure s \ s`,
or the union of `s` and the complement of `∂(s)`.
This is the largest set such that `s` is closed in, and `s` is locally closed if and only if
`coborder s` is open.

This is unnamed in the literature, and this name is due to the fact that `coborder s = (border sᶜ)ᶜ`
where `border s = s \ interior s` is the border in the sense of Hausdorff.
-/
def coborder (s : Set α) : Set α :=
  (closure s \ s)ᶜ

lemma subset_coborder :
    s ⊆ coborder s := by
  rw [coborder, Set.subset_compl_iff_disjoint_right]
  exact disjoint_sdiff_self_right

lemma coborder_inter_closure :
    coborder s ∩ closure s = s := by
  rw [coborder, ← Set.diff_eq_compl_inter, Set.diff_diff_right_self, Set.inter_eq_right]
  exact subset_closure

lemma closure_inter_coborder :
    closure s ∩ coborder s = s := by
  rw [Set.inter_comm, coborder_inter_closure]

lemma coborder_eq_union_frontier_compl :
    coborder s = s ∪ (frontier s)ᶜ := by
  rw [coborder, compl_eq_comm, Set.compl_union, compl_compl, ← Set.diff_eq_compl_inter,
    ← Set.union_diff_right, Set.union_comm, ← closure_eq_self_union_frontier]

lemma coborder_eq_univ_iff :
    coborder s = Set.univ ↔ IsClosed s := by
  simp [coborder, Set.diff_eq_empty, closure_subset_iff_isClosed]

alias ⟨_, IsClosed.coborder_eq⟩ := coborder_eq_univ_iff

lemma coborder_eq_compl_frontier_iff :
    coborder s = (frontier s)ᶜ ↔ IsOpen s := by
  simp only [coborder, compl_inj_iff, frontier, sdiff_eq_sdiff_iff_inf_eq_inf, Set.inf_eq_inter]
  rw [Set.inter_eq_right.mpr (interior_subset.trans subset_closure),
    Set.inter_eq_right.mpr subset_closure, eq_comm, interior_eq_iff_isOpen]

alias ⟨_, IsOpen.coborder_eq⟩ := coborder_eq_compl_frontier_iff

lemma IsOpenMap.coborder_preimage_subset (hf : IsOpenMap f) (s : Set β) :
    coborder (f ⁻¹' s) ⊆ f ⁻¹' (coborder s) := by
  rw [coborder, coborder, Set.preimage_compl, Set.preimage_diff, Set.compl_subset_compl]
  apply Set.diff_subset_diff_left
  exact hf.preimage_closure_subset_closure_preimage

lemma Continuous.preimage_coborder_subset (hf : Continuous f) (s : Set β) :
    f ⁻¹' (coborder s) ⊆ coborder (f ⁻¹' s) := by
  rw [coborder, coborder, Set.preimage_compl, Set.preimage_diff, Set.compl_subset_compl]
  apply Set.diff_subset_diff_left
  exact hf.closure_preimage_subset s

lemma coborder_preimage (hf : IsOpenMap f) (hf' : Continuous f) (s : Set β) :
    coborder (f ⁻¹' s) = f ⁻¹' (coborder s) :=
  (hf.coborder_preimage_subset s).antisymm (hf'.preimage_coborder_subset s)

protected
lemma OpenEmbedding.coborder_preimage (hf : OpenEmbedding f) (s : Set β) :
    coborder (f ⁻¹' s) = f ⁻¹' (coborder s) :=
  coborder_preimage hf.isOpenMap hf.continuous s

lemma isClosed_preimage_val : IsClosed (s ↓∩ t) ↔ s ∩ closure (s ∩ t) ⊆ t := by
  rw [← closure_eq_iff_isClosed, embedding_subtype_val.closure_eq_preimage_closure_image,
    ← (Set.image_injective.mpr Subtype.val_injective).eq_iff, Subtype.image_preimage_coe,
    Subtype.image_preimage_coe, subset_antisymm_iff, and_iff_left, Set.subset_inter_iff,
    and_iff_right]
  exacts [Set.inter_subset_left, Set.subset_inter Set.inter_subset_left subset_closure]

lemma isClosed_preimage_val_coborder :
    IsClosed (coborder s ↓∩ s) := by
  rw [isClosed_preimage_val, Set.inter_eq_right.mpr subset_coborder, coborder_inter_closure]

/--
A set is locally closed if it is the intersection of some open set and some closed set.
Also see `isLocallyClosed_tfae`.
-/
def IsLocallyClosed (s : Set α) : Prop := ∃ (U Z : Set α), IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z

lemma IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocallyClosed s :=
  ⟨_, _, hs, isClosed_univ, (Set.inter_univ _).symm⟩

lemma IsClosed.isLocallyClosed (hs : IsClosed s) : IsLocallyClosed s :=
  ⟨_, _, isOpen_univ, hs, (Set.univ_inter _).symm⟩

lemma IsLocallyClosed.inter (hs : IsLocallyClosed s) (ht : IsLocallyClosed t) :
    IsLocallyClosed (s ∩ t) := by
  obtain ⟨U₁, Z₁, hU₁, hZ₁, rfl⟩ := hs
  obtain ⟨U₂, Z₂, hU₂, hZ₂, rfl⟩ := ht
  refine ⟨_, _, hU₁.inter hU₂, hZ₁.inter hZ₂, Set.inter_inter_inter_comm U₁ Z₁ U₂ Z₂⟩

lemma IsLocallyClosed.preimage {s : Set β} (hs : IsLocallyClosed s)
    {f : α → β} (hf : Continuous f) :
    IsLocallyClosed (f ⁻¹' s) := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  exact ⟨_, _, hU.preimage hf, hZ.preimage hf, Set.preimage_inter⟩

nonrec
lemma Inducing.isLocallyClosed_iff {s : Set α}
    {f : α → β} (hf : Inducing f) :
    IsLocallyClosed s ↔ ∃ s' : Set β, IsLocallyClosed s' ∧ f ⁻¹' s' = s := by
  simp_rw [IsLocallyClosed, hf.isOpen_iff, hf.isClosed_iff]
  constructor
  · rintro ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩

lemma Embedding.isLocallyClosed_iff {s : Set α}
    {f : α → β} (hf : Embedding f) :
    IsLocallyClosed s ↔ ∃ s' : Set β, IsLocallyClosed s' ∧ s' ∩ Set.range f = f '' s := by
  simp_rw [hf.toInducing.isLocallyClosed_iff,
    ← (Set.image_injective.mpr hf.inj).eq_iff, Set.image_preimage_eq_inter_range]

lemma IsLocallyClosed.image {s : Set α} (hs : IsLocallyClosed s)
    {f : α → β} (hf : Inducing f) (hf' : IsLocallyClosed (Set.range f)) :
    IsLocallyClosed (f '' s) := by
  obtain ⟨t, ht, rfl⟩ := hf.isLocallyClosed_iff.mp hs
  rw [Set.image_preimage_eq_inter_range]
  exact ht.inter hf'

/--
A set `s` is locally closed if one of the equivalent conditions below hold
1. It is the intersection of some open set and some closed set.
2. The coborder `(closure s \ s)ᶜ` is open.
3. `s` is closed in some neighborhood of `x` for all `x ∈ s`.
4. Every `x ∈ s` has some open neighborhood `U` such that `U ∩ closure s ⊆ s`.
5. `s` is open in the closure of `s`.
-/
lemma isLocallyClosed_tfae (s : Set α) :
    List.TFAE
    [ IsLocallyClosed s,
      IsOpen (coborder s),
      ∀ x ∈ s, ∃ U ∈ 𝓝 x, IsClosed (U ↓∩ s),
      ∀ x ∈ s, ∃ U, x ∈ U ∧ IsOpen U ∧ U ∩ closure s ⊆ s,
      IsOpen (closure s ↓∩ s)] := by
  tfae_have 1 → 2
  · rintro ⟨U, Z, hU, hZ, rfl⟩
    have : Z ∪ (frontier (U ∩ Z))ᶜ = Set.univ := by
      nth_rw 1 [← hZ.closure_eq]
      rw [← Set.compl_subset_iff_union, Set.compl_subset_compl]
      refine frontier_subset_closure.trans (closure_mono Set.inter_subset_right)
    rw [coborder_eq_union_frontier_compl, Set.inter_union_distrib_right, this,
      Set.inter_univ]
    exact hU.union isClosed_frontier.isOpen_compl
  tfae_have 2 → 3
  · exact fun h x ↦ (⟨coborder s, h.mem_nhds <| subset_coborder ·, isClosed_preimage_val_coborder⟩)
  tfae_have 3 → 4
  · intro h x hx
    obtain ⟨t, ht, ht'⟩ := h x hx
    obtain ⟨U, hUt, hU, hxU⟩ := mem_nhds_iff.mp ht
    rw [isClosed_preimage_val] at ht'
    exact ⟨U, hxU, hU, (Set.subset_inter (Set.inter_subset_left.trans hUt) (hU.inter_closure.trans
      (closure_mono <| Set.inter_subset_inter hUt subset_rfl))).trans ht'⟩
  tfae_have 4 → 5
  · intro H
    choose U hxU hU e using H
    refine ⟨⋃ x ∈ s, U x ‹_›, isOpen_iUnion (isOpen_iUnion <| hU ·), Set.ext fun x ↦ ⟨?_, ?_⟩⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, ⟨_, ⟨hy, rfl⟩, hxU⟩⟩⟩
      exact e y hy ⟨hxU, x.2⟩
    · exact (Set.subset_iUnion₂ _ _ <| hxU x ·)
  tfae_have 5 → 1
  · intro H
    convert H.isLocallyClosed.image inducing_subtype_val
      (by simpa using isClosed_closure.isLocallyClosed)
    simpa using subset_closure
  tfae_finish

lemma isLocallyClosed_iff_isOpen_coborder : IsLocallyClosed s ↔ IsOpen (coborder s) :=
  (isLocallyClosed_tfae s).out 0 1

alias ⟨IsLocallyClosed.isOpen_coborder, _⟩ := isLocallyClosed_iff_isOpen_coborder

lemma IsLocallyClosed.isOpen_preimage_val_closure (hs : IsLocallyClosed s) :
    IsOpen (closure s ↓∩ s) :=
  ((isLocallyClosed_tfae s).out 0 4).mp hs

open TopologicalSpace

variable {ι : Type*} {U : ι → Opens β} (hU : iSup U = ⊤)

theorem isLocallyClosed_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsLocallyClosed s ↔ ∀ i, IsLocallyClosed ((↑) ⁻¹' s : Set (U i)) := by
  simp_rw [isLocallyClosed_iff_isOpen_coborder]
  rw [isOpen_iff_coe_preimage_of_iSup_eq_top hU]
  exact forall_congr' fun i ↦ by rw [(U i).isOpen.openEmbedding_subtype_val.coborder_preimage]
