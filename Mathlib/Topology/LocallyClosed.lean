/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Constructions
import Mathlib.Tactic.TFAE

/-!
# Locally closed sets

## Main definitions

* `IsLocallyClosed`: Predicate saying that a set is locally closed

## Main results

* `isLocallyClosed_tfae`:
  A set `s` is locally closed if one of the equivalent conditions below hold
  1. It is the intersection of some open set and some closed set.
  2. The coborder `(closure s \ s)ᶜ` is open.
  3. `s` is closed in some neighborhood of `x` for all `x ∈ s`.
  4. Every `x ∈ s` has some open neighborhood `U` such that `U ∩ closure s ⊆ s`.
  5. `s` is open in the closure of `s`.

-/

open Set Topology
open scoped Set.Notation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X → Y}

lemma subset_coborder :
    s ⊆ coborder s := by
  rw [coborder, subset_compl_iff_disjoint_right]
  exact disjoint_sdiff_self_right

lemma coborder_inter_closure :
    coborder s ∩ closure s = s := by
  rw [coborder, ← diff_eq_compl_inter, diff_diff_right_self, inter_eq_right]
  exact subset_closure

lemma closure_inter_coborder :
    closure s ∩ coborder s = s := by
  rw [inter_comm, coborder_inter_closure]

lemma coborder_eq_union_frontier_compl :
    coborder s = s ∪ (frontier s)ᶜ := by
  rw [coborder, compl_eq_comm, compl_union, compl_compl, ← diff_eq_compl_inter,
    ← union_diff_right, union_comm, ← closure_eq_self_union_frontier]

lemma coborder_eq_univ_iff :
    coborder s = univ ↔ IsClosed s := by
  simp [coborder, diff_eq_empty, closure_subset_iff_isClosed]

alias ⟨_, IsClosed.coborder_eq⟩ := coborder_eq_univ_iff

lemma coborder_eq_compl_frontier_iff :
    coborder s = (frontier s)ᶜ ↔ IsOpen s := by
  simp_rw [coborder_eq_union_frontier_compl, union_eq_right, subset_compl_iff_disjoint_left,
    disjoint_frontier_iff_isOpen]

theorem coborder_eq_union_closure_compl {s : Set X} : coborder s = s ∪ (closure s)ᶜ := by
  rw [coborder, compl_eq_comm, compl_union, compl_compl, inter_comm]
  rfl

/-- The coborder of any set is dense -/
theorem dense_coborder {s : Set X} :
    Dense (coborder s) := by
  rw [dense_iff_closure_eq, coborder_eq_union_closure_compl, closure_union, ← univ_subset_iff]
  refine _root_.subset_trans ?_ (union_subset_union_right _ (subset_closure))
  simp

alias ⟨_, IsOpen.coborder_eq⟩ := coborder_eq_compl_frontier_iff

lemma IsOpenMap.coborder_preimage_subset (hf : IsOpenMap f) (s : Set Y) :
    coborder (f ⁻¹' s) ⊆ f ⁻¹' (coborder s) := by
  rw [coborder, coborder, preimage_compl, preimage_diff, compl_subset_compl]
  apply diff_subset_diff_left
  exact hf.preimage_closure_subset_closure_preimage

lemma Continuous.preimage_coborder_subset (hf : Continuous f) (s : Set Y) :
    f ⁻¹' (coborder s) ⊆ coborder (f ⁻¹' s) := by
  rw [coborder, coborder, preimage_compl, preimage_diff, compl_subset_compl]
  apply diff_subset_diff_left
  exact hf.closure_preimage_subset s

lemma coborder_preimage (hf : IsOpenMap f) (hf' : Continuous f) (s : Set Y) :
    coborder (f ⁻¹' s) = f ⁻¹' (coborder s) :=
  (hf.coborder_preimage_subset s).antisymm (hf'.preimage_coborder_subset s)

protected
lemma Topology.IsOpenEmbedding.coborder_preimage (hf : IsOpenEmbedding f) (s : Set Y) :
    coborder (f ⁻¹' s) = f ⁻¹' coborder s :=
  coborder_preimage hf.isOpenMap hf.continuous s

lemma isClosed_preimage_val_coborder :
    IsClosed (coborder s ↓∩ s) := by
  rw [isClosed_preimage_val, inter_eq_right.mpr subset_coborder, coborder_inter_closure]

lemma IsLocallyClosed.inter (hs : IsLocallyClosed s) (ht : IsLocallyClosed t) :
    IsLocallyClosed (s ∩ t) := by
  obtain ⟨U₁, Z₁, hU₁, hZ₁, rfl⟩ := hs
  obtain ⟨U₂, Z₂, hU₂, hZ₂, rfl⟩ := ht
  refine ⟨_, _, hU₁.inter hU₂, hZ₁.inter hZ₂, inter_inter_inter_comm U₁ Z₁ U₂ Z₂⟩

lemma IsLocallyClosed.preimage {s : Set Y} (hs : IsLocallyClosed s)
    {f : X → Y} (hf : Continuous f) :
    IsLocallyClosed (f ⁻¹' s) := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  exact ⟨_, _, hU.preimage hf, hZ.preimage hf, preimage_inter⟩

nonrec
lemma Topology.IsInducing.isLocallyClosed_iff {s : Set X}
    {f : X → Y} (hf : IsInducing f) :
    IsLocallyClosed s ↔ ∃ s' : Set Y, IsLocallyClosed s' ∧ f ⁻¹' s' = s := by
  simp_rw [IsLocallyClosed, hf.isOpen_iff, hf.isClosed_iff]
  constructor
  · rintro ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩

@[deprecated (since := "2024-10-28")]
alias Inducing.isLocallyClosed_iff := IsInducing.isLocallyClosed_iff

lemma Topology.IsEmbedding.isLocallyClosed_iff {s : Set X}
    {f : X → Y} (hf : IsEmbedding f) :
    IsLocallyClosed s ↔ ∃ s' : Set Y, IsLocallyClosed s' ∧ s' ∩ range f = f '' s := by
  simp_rw [hf.isInducing.isLocallyClosed_iff,
    ← (image_injective.mpr hf.injective).eq_iff, image_preimage_eq_inter_range]

@[deprecated (since := "2024-10-26")]
alias Embedding.isLocallyClosed_iff := IsEmbedding.isLocallyClosed_iff

lemma IsLocallyClosed.image {s : Set X} (hs : IsLocallyClosed s)
    {f : X → Y} (hf : IsInducing f) (hf' : IsLocallyClosed (range f)) :
    IsLocallyClosed (f '' s) := by
  obtain ⟨t, ht, rfl⟩ := hf.isLocallyClosed_iff.mp hs
  rw [image_preimage_eq_inter_range]
  exact ht.inter hf'

/--
A set `s` is locally closed if one of the equivalent conditions below hold
1. It is the intersection of some open set and some closed set.
2. The coborder `(closure s \ s)ᶜ` is open.
3. `s` is closed in some neighborhood of `x` for all `x ∈ s`.
4. Every `x ∈ s` has some open neighborhood `U` such that `U ∩ closure s ⊆ s`.
5. `s` is open in the closure of `s`.
-/
lemma isLocallyClosed_tfae (s : Set X) :
    List.TFAE
    [ IsLocallyClosed s,
      IsOpen (coborder s),
      ∀ x ∈ s, ∃ U ∈ 𝓝 x, IsClosed (U ↓∩ s),
      ∀ x ∈ s, ∃ U, x ∈ U ∧ IsOpen U ∧ U ∩ closure s ⊆ s,
      IsOpen (closure s ↓∩ s)] := by
  tfae_have 1 → 2 := by
    rintro ⟨U, Z, hU, hZ, rfl⟩
    have : Z ∪ (frontier (U ∩ Z))ᶜ = univ := by
      nth_rw 1 [← hZ.closure_eq]
      rw [← compl_subset_iff_union, compl_subset_compl]
      refine frontier_subset_closure.trans (closure_mono inter_subset_right)
    rw [coborder_eq_union_frontier_compl, inter_union_distrib_right, this,
      inter_univ]
    exact hU.union isClosed_frontier.isOpen_compl
  tfae_have 2 → 3
  | h, x => (⟨coborder s, h.mem_nhds <| subset_coborder ·, isClosed_preimage_val_coborder⟩)
  tfae_have 3 → 4
  | h, x, hx => by
    obtain ⟨t, ht, ht'⟩ := h x hx
    obtain ⟨U, hUt, hU, hxU⟩ := mem_nhds_iff.mp ht
    rw [isClosed_preimage_val] at ht'
    exact ⟨U, hxU, hU, (subset_inter (inter_subset_left.trans hUt) (hU.inter_closure.trans
      (closure_mono <| inter_subset_inter hUt subset_rfl))).trans ht'⟩
  tfae_have 4 → 5
  | H => by
    choose U hxU hU e using H
    refine ⟨⋃ x ∈ s, U x ‹_›, isOpen_iUnion (isOpen_iUnion <| hU ·), ext fun x ↦ ⟨?_, ?_⟩⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, ⟨_, ⟨hy, rfl⟩, hxU⟩⟩⟩
      exact e y hy ⟨hxU, x.2⟩
    · exact (subset_iUnion₂ _ _ <| hxU x ·)
  tfae_have 5 → 1
  | H => by
    convert H.isLocallyClosed.image IsInducing.subtypeVal
      (by simpa using isClosed_closure.isLocallyClosed)
    simpa using subset_closure
  tfae_finish

lemma isLocallyClosed_iff_isOpen_coborder : IsLocallyClosed s ↔ IsOpen (coborder s) :=
  (isLocallyClosed_tfae s).out 0 1

alias ⟨IsLocallyClosed.isOpen_coborder, _⟩ := isLocallyClosed_iff_isOpen_coborder

lemma IsLocallyClosed.isOpen_preimage_val_closure (hs : IsLocallyClosed s) :
    IsOpen (closure s ↓∩ s) :=
  ((isLocallyClosed_tfae s).out 0 4).mp hs
