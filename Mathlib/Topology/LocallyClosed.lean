/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Topology.Constructions
public import Mathlib.Tactic.TFAE

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

public section

open Set Topology Filter
open scoped Set.Notation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X → Y}

section coborder

lemma mem_coborder_iff_imp {x : X} :
    x ∈ coborder s ↔ x ∈ closure s → x ∈ s := by
  simp [coborder]

lemma subset_coborder :
    s ⊆ coborder s := by
  rw [coborder, subset_compl_iff_disjoint_right]
  exact disjoint_sdiff_self_right

lemma coborder_inter_closure :
    coborder s ∩ closure s = s := by
  rw [coborder, ← sdiff_eq_compl_inter, sdiff_sdiff_right_self, inter_eq_right]
  exact subset_closure

lemma closure_inter_coborder :
    closure s ∩ coborder s = s := by
  rw [inter_comm, coborder_inter_closure]

lemma coborder_eq_union_frontier_compl :
    coborder s = s ∪ (frontier s)ᶜ := by
  rw [coborder, compl_eq_comm, compl_union, compl_compl, ← sdiff_eq_compl_inter,
    ← union_sdiff_right, union_comm, ← closure_eq_self_union_frontier]

lemma coborder_eq_univ_iff :
    coborder s = univ ↔ IsClosed s := by
  simp [coborder, sdiff_eq_empty, closure_subset_iff_isClosed]

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
  rw [coborder, coborder, preimage_compl, preimage_sdiff, compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.preimage_closure_subset_closure_preimage

lemma Continuous.preimage_coborder_subset (hf : Continuous f) (s : Set Y) :
    f ⁻¹' (coborder s) ⊆ coborder (f ⁻¹' s) := by
  rw [coborder, coborder, preimage_compl, preimage_sdiff, compl_subset_compl]
  apply sdiff_subset_sdiff_left
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

end coborder

section IsLocallyClosedAt

lemma IsLocallyClosedAt.of_mem_nhds {x : X} (hx : s ∈ 𝓝 x) :
    IsLocallyClosedAt s x :=
  ⟨s, univ, hx, isClosed_univ, by simp⟩

lemma IsLocallyClosedAt.of_notMem_closure {x : X} (hx : x ∉ closure s) :
    IsLocallyClosedAt s x :=
  ⟨(closure s)ᶜ, closure s, isClosed_closure.isOpen_compl.mem_nhds hx, isClosed_closure, by
    simp [← disjoint_iff_inter_eq_empty, disjoint_compl_left_iff, subset_closure]⟩

lemma isLocallyClosedAt_tfae (s : Set X) (x : X) :
    List.TFAE
    [ IsLocallyClosedAt s x,
      ∃ U ∈ 𝓝 x, IsClosed (U ↓∩ s),
      ∀ᶠ U in (𝓝 x).smallSets, IsClosed (U ↓∩ s),
      ∃ U ∈ 𝓝 x, U ∩ closure s ⊆ s,
      ∀ᶠ U in (𝓝 x).smallSets, U ∩ closure s ⊆ s,
      ∃ U ∈ 𝓝 x, U ∩ closure s = U ∩ s,
      ∀ᶠ U in (𝓝 x).smallSets, U ∩ closure s = U ∩ s,
      closure s =ᶠ[𝓝 x] s,
      closure s ≤ᶠ[𝓝 x] s,
      coborder s ∈ 𝓝 x] := by
  have mono (U V : Set X) (U_sub_V : U ⊆ V) (h : IsClosed (V ↓∩ s)) : IsClosed (U ↓∩ s) :=
    h.preimage <| continuous_inclusion U_sub_V
  tfae_have 1 → 2 := by
    rintro ⟨U, Z, U_mem, Z_closed, eq⟩
    use U, U_mem
    exact IsInducing.subtypeVal.isClosed_iff.mpr
      ⟨Z, Z_closed, by simp [Subtype.preimage_val_eq_preimage_val_iff, eq]⟩
  tfae_have 2 ↔ 3 := by
    rw [eventually_smallSets' mono]
  tfae_have 3 → 4 := by
    intro H
    rw [nhds_basis_opens' x |>.eventually_smallSets mono] at H
    obtain ⟨U, ⟨U_mem, U_open⟩, H⟩ := H
    rw [← closure_subset_iff_isClosed,
      ← U_open.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage (by fun_prop),
      Subtype.preimage_val_subset_preimage_val_iff] at H
    exact ⟨U, U_mem, by simpa using H⟩
  tfae_have 4 ↔ 5 := by grind [eventually_smallSets']
  tfae_have 4 ↔ 6 := by grind [subset_closure]
  tfae_have 6 → 1 := by
    rintro ⟨U, U_mem, eq⟩
    exact ⟨U, closure s, U_mem, isClosed_closure, eq.symm⟩
  tfae_have 5 ↔ 7 := by grind [subset_closure]
  tfae_have 6 ↔ 8 := by simp [eventuallyEq_set, eventually_iff_exists_mem, Set.ext_iff]
  tfae_have 8 → 9 := fun H ↦ H.le
  tfae_have 9 → 8 := fun H ↦ H.antisymm <| .of_forall subset_closure
  tfae_have 9 ↔ 10 := by
    simp_rw [← eventually_mem_set, mem_coborder_iff_imp]
    rfl
  tfae_finish

end IsLocallyClosedAt

section IsLocallyClosed

lemma IsLocallyClosed.isLocallyClosedAt (hs : IsLocallyClosed s) {x : X} (hx : x ∈ s) :
    IsLocallyClosedAt s x := by
  obtain ⟨U, Z, U_open, Z_closed, s_eq⟩ := hs
  exact ⟨U, Z, U_open.mem_nhds (s_eq ▸ hx).1, Z_closed, by simp [s_eq]⟩

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

lemma Topology.IsInducing.isLocallyClosed_iff {s : Set X}
    {f : X → Y} (hf : IsInducing f) :
    IsLocallyClosed s ↔ ∃ s' : Set Y, IsLocallyClosed s' ∧ f ⁻¹' s' = s := by
  simp_rw [IsLocallyClosed, hf.isOpen_iff, hf.isClosed_iff]
  constructor
  · rintro ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩

lemma Topology.IsEmbedding.isLocallyClosed_iff {s : Set X}
    {f : X → Y} (hf : IsEmbedding f) :
    IsLocallyClosed s ↔ ∃ s' : Set Y, IsLocallyClosed s' ∧ s' ∩ range f = f '' s := by
  simp_rw [hf.isInducing.isLocallyClosed_iff,
    ← (image_injective.mpr hf.injective).eq_iff, image_preimage_eq_inter_range]

lemma IsLocallyClosed.image {s : Set X} (hs : IsLocallyClosed s)
    {f : X → Y} (hf : IsInducing f) (hf' : IsLocallyClosed (range f)) :
    IsLocallyClosed (f '' s) := by
  obtain ⟨t, ht, rfl⟩ := hf.isLocallyClosed_iff.mp hs
  rw [image_preimage_eq_inter_range]
  exact ht.inter hf'

/--
A set `s` is locally closed if one of the equivalent conditions below hold
1. It is the intersection of some open set and some closed set (this is the definition).
2. It is locally closed at each of its points.
3. It is locally closed at each point of its coborder
4. The coborder `(closure s \ s)ᶜ` is open.
5. `s` is the intersection of an open set and `closure s`.
6. `s` is open in the closure of `s`.
-/
lemma isLocallyClosed_tfae (s : Set X) :
    List.TFAE
    [ IsLocallyClosed s,
      ∀ x ∈ s, IsLocallyClosedAt s x,
      ∀ x ∈ coborder s, IsLocallyClosedAt s x,
      IsOpen (coborder s),
      ∃ U, IsOpen U ∧ s = U ∩ closure s,
      IsOpen (closure s ↓∩ s)] := by
  tfae_have 1 → 2 := fun H x ↦ H.isLocallyClosedAt
  tfae_have 2 → 3 := fun H x hx ↦ by
    rw [coborder, compl_sdiff, mem_union] at hx
    exact hx.elim (H x) (fun hx ↦ .of_notMem_closure hx)
  tfae_have 3 ↔ 4 := by
    simp [isOpen_iff_mem_nhds, (isLocallyClosedAt_tfae s _) |>.out 0 9]
  tfae_have 4 → 5 := fun H ↦ ⟨coborder s, H, by rw [coborder_inter_closure]⟩
  tfae_have 5 → 1 := fun ⟨U, U_open, eq⟩ ↦ ⟨U, closure s, U_open, isClosed_closure, eq⟩
  tfae_have 5 ↔ 6 := by
    simp [IsInducing.subtypeVal.isOpen_iff, Subtype.preimage_val_eq_preimage_val_iff,
      inter_eq_right.mpr subset_closure, inter_comm, eq_comm]
  tfae_finish

lemma isLocallyClosed_iff_isOpen_coborder : IsLocallyClosed s ↔ IsOpen (coborder s) :=
  (isLocallyClosed_tfae s).out 0 3

alias ⟨IsLocallyClosed.isOpen_coborder, _⟩ := isLocallyClosed_iff_isOpen_coborder

lemma IsLocallyClosed.isOpen_preimage_val_closure (hs : IsLocallyClosed s) :
    IsOpen (closure s ↓∩ s) :=
  ((isLocallyClosed_tfae s).out 0 5).mp hs

end IsLocallyClosed
