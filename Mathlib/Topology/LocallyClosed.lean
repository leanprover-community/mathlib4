/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Anatole Dedecker
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Tactic.TFAE

/-!
# Locally closed sets

In this file, we develop API for the predicates `IsLocallyClosedAt`, expressing that
a set is locally closed at a point, and `IsLocallyClosed`, expressing that a set is locally closed.
These are defined earlier, but most of their API should be in this file.

## Main results

* `isLocallyClosedAt_tfae`:
  A set `s` is locally closed at a point `x` if one of the equivalent conditions below hold
  1. There is a neighborhood `U` of `x` such that `U ∩ s` can be written `U ∩ Z` for some closed set
    `Z` (this is the definition).
  2. There is a neighborhood `U` of `x` such that `U ∩ s` is a closed subset of `U`.
  3. There is a neighborhood `U` of `x` such that `U ∩ closure s ⊆ s`.
  4. There is a neighborhood `U` of `x` such that `U ∩ s = U ∩ closure s`.
  5. `s` coincides with some closed set `Z` eventually near `x`.
  6. `s` and `closure s` coincide eventually near `x`.
  7. `closure s ⊆ s` eventually near `x`.
  8. `s` is a neighborhood of `x` inside `closure s`.
  9. `coborder s` is a neighborhood of `x`.
* `isLocallyClosed_tfae`:
  A set `s` is locally closed if one of the equivalent conditions below hold
  1. It is the intersection of some open set and some closed set (this is the definition).
  2. It is locally closed at each of its points.
  3. It is locally closed at each point of its coborder.
  4. The coborder `(closure s \ s)ᶜ` is open.
  5. `s` is the intersection of an open set and `closure s`.
  6. `s` is open in the closure of `s`.

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
  ⟨s, hx, univ, isClosed_univ, by simp⟩

lemma IsLocallyClosedAt.of_notMem_closure {x : X} (hx : x ∉ closure s) :
    IsLocallyClosedAt s x :=
  ⟨(closure s)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hx, closure s, isClosed_closure, by
    simp [← disjoint_iff_inter_eq_empty, disjoint_compl_left_iff, subset_closure]⟩

lemma IsLocallyClosedAt.preimage {x : X} {s : Set Y} {f : X → Y}
    (hs : IsLocallyClosedAt s (f x))
    (hf : Continuous f) :
    IsLocallyClosedAt (f ⁻¹' s) x := by
  obtain ⟨U, hU, Z, hZ, eq⟩ := hs
  exact ⟨_, hf.tendsto x hU, _, hZ.preimage hf, by simp [← preimage_inter, eq]⟩

/-- A set `s` is locally closed at a point `x` if one of the equivalent conditions below hold
1. There is a neighborhood `U` of `x` such that `U ∩ s` can be written `U ∩ Z` for some closed set
  `Z` (this is the definition).
2. There is a neighborhood `U` of `x` such that `U ∩ s` is a closed subset of `U`.
3. There is a neighborhood `U` of `x` such that `U ∩ closure s ⊆ s`.
4. There is a neighborhood `U` of `x` such that `U ∩ s = U ∩ closure s`.
5. `s` coincides with some closed set `Z` eventually near `x`.
6. `s` and `closure s` coincide eventually near `x`.
7. `closure s ⊆ s` eventually near `x`.
8. `s` is a neighborhood of `x` inside `closure s`.
9. `coborder s` is a neighborhood of `x`.

Furthermore (see API below), in assertions 1, 2, 3 and 4, one can restrict to `U` belonging
to a basis of neighborhoods of `x`.
-/
lemma isLocallyClosedAt_tfae (s : Set X) (x : X) :
    List.TFAE
    [ IsLocallyClosedAt s x,
      ∃ U ∈ 𝓝 x, IsClosed (U ↓∩ s),
      ∃ U ∈ 𝓝 x, U ∩ closure s ⊆ s,
      ∃ U ∈ 𝓝 x, U ∩ s = U ∩ closure s,
      ∃ Z, IsClosed Z ∧ s =ᶠ[𝓝 x] Z,
      s =ᶠ[𝓝 x] closure s,
      closure s ≤ᶠ[𝓝 x] s,
      s ∈ 𝓝[closure s] x,
      coborder s ∈ 𝓝 x] := by
  tfae_have 1 ↔ 2 := by
    simp [IsLocallyClosedAt, IsInducing.subtypeVal.isClosed_iff,
      Subtype.preimage_val_eq_preimage_val_iff, eq_comm]
  tfae_have 2 → 3 := by
    intro H
    have (U V : Set X) (U_sub_V : U ⊆ V) (h : IsClosed (V ↓∩ s)) : IsClosed (U ↓∩ s) :=
      h.preimage <| continuous_inclusion U_sub_V
    rw [nhds_basis_opens' x |>.exists_iff this] at H
    obtain ⟨U, ⟨U_mem, U_open⟩, H⟩ := H
    rw [← closure_subset_iff_isClosed,
      ← U_open.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage (by fun_prop),
      Subtype.preimage_val_subset_preimage_val_iff] at H
    exact ⟨U, U_mem, by simpa using H⟩
  tfae_have 3 ↔ 4 := by grind [subset_closure]
  tfae_have 4 → 1 := by
    rintro ⟨U, U_mem, eq⟩
    exact ⟨U, U_mem, closure s, isClosed_closure, eq⟩
  tfae_have 1 ↔ 5 := by
    simp only [IsLocallyClosedAt, Set.ext_iff, mem_inter_iff, and_congr_right_iff,
      eventuallyEqSet_iff, eventually_iff_exists_mem]
    grind
  tfae_have 4 ↔ 6 := by simp [eventuallyEqSet_iff, eventually_iff_exists_mem, Set.ext_iff]
  tfae_have 6 → 7 := fun H ↦ H.symm.le
  tfae_have 7 → 6 := fun H ↦ EventuallyLE.antisymm (.of_forall subset_closure) H
  tfae_have 7 ↔ 8 := by
    simp_rw [← eventually_mem_set, eventually_nhdsWithin_iff]
    rfl
  tfae_have 8 ↔ 9 := by
    simp_rw [← eventually_mem_set, eventually_nhdsWithin_iff, mem_coborder_iff_imp]
  tfae_finish

lemma isLocallyClosedAt_iff_exists_isClosed_preimage_val {x : X} : IsLocallyClosedAt s x ↔
    ∃ U ∈ 𝓝 x, IsClosed (U ↓∩ s) :=
  (isLocallyClosedAt_tfae s x).out 1 2

lemma isLocallyClosedAt_iff_exists_inter_closure_subset {x : X} : IsLocallyClosedAt s x ↔
    ∃ U ∈ 𝓝 x, U ∩ closure s ⊆ s :=
  (isLocallyClosedAt_tfae s x).out 1 3

lemma isLocallyClosedAt_iff_exists_eq_inter_closure {x : X} : IsLocallyClosedAt s x ↔
    ∃ U ∈ 𝓝 x, U ∩ s = U ∩ closure s :=
  (isLocallyClosedAt_tfae s x).out 1 4

lemma isLocallyClosedAt_iff_exists_isClosed_inter_eq_of_hasBasis {ι : Type*} {p : ι → Prop}
    {U : ι → Set X} {x : X} (H : (𝓝 x).HasBasis p U) : IsLocallyClosedAt s x ↔
    ∃ i, p i ∧ ∃ Z, IsClosed Z ∧ U i ∩ s = U i ∩ Z := by
  have (U V : Set X) (U_sub_V : U ⊆ V) (h : ∃ Z, IsClosed Z ∧ V ∩ s = V ∩ Z) :
      ∃ Z, IsClosed Z ∧ U ∩ s = U ∩ Z :=
    h.imp fun Z hZ ↦ hZ.imp_right fun eq ↦ inter_eq_inter_mono_left eq U_sub_V
  rw [IsLocallyClosedAt, H.exists_iff this]

lemma isLocallyClosedAt_iff_exists_isClosed_preimage_val_of_hasBasis {ι : Type*} {p : ι → Prop}
    {U : ι → Set X} {x : X} (H : (𝓝 x).HasBasis p U) : IsLocallyClosedAt s x ↔
    ∃ i, p i ∧ IsClosed (U i ↓∩ s) := by
  have (U V : Set X) (U_sub_V : U ⊆ V) (h : IsClosed (V ↓∩ s)) : IsClosed (U ↓∩ s) :=
    h.preimage <| continuous_inclusion U_sub_V
  rw [isLocallyClosedAt_iff_exists_isClosed_preimage_val, H.exists_iff this]

lemma isLocallyClosedAt_iff_exists_inter_closure_subset_of_hasBasis {ι : Type*} {p : ι → Prop}
    {U : ι → Set X} {x : X} (H : (𝓝 x).HasBasis p U) : IsLocallyClosedAt s x ↔
    ∃ i, p i ∧ U i ∩ closure s ⊆ s := by
  have (U V : Set X) (U_sub_V : U ⊆ V) (h : V ∩ closure s ⊆ s) : U ∩ closure s ⊆ s :=
    subset_trans (inter_subset_inter_left _ U_sub_V) h
  rw [isLocallyClosedAt_iff_exists_inter_closure_subset, H.exists_iff this]

lemma isLocallyClosedAt_iff_exists_eq_inter_closure_of_hasBasis {ι : Type*} {p : ι → Prop}
    {U : ι → Set X} {x : X} (H : (𝓝 x).HasBasis p U) : IsLocallyClosedAt s x ↔
    ∃ i, p i ∧ U i ∩ s = U i ∩ closure s := by
  have (U V : Set X) (U_sub_V : U ⊆ V) (h : V ∩ s = V ∩ closure s) : U ∩ s = U ∩ closure s :=
    inter_eq_inter_mono_left h U_sub_V
  rw [isLocallyClosedAt_iff_exists_eq_inter_closure, H.exists_iff this]

lemma isLocallyClosedAt_iff_exists_isClosed_eventuallyEqSet {x : X} : IsLocallyClosedAt s x ↔
    ∃ Z, IsClosed Z ∧ s =ᶠ[𝓝 x] Z :=
  (isLocallyClosedAt_tfae s x).out 1 5

@[deprecated (since := "2026-09-02")]
alias isLocallyClosedAt_iff_exists_isClosed_eventuallyEq :=
  isLocallyClosedAt_iff_exists_isClosed_eventuallyEqSet

lemma isLocallyClosedAt_iff_eventuallyEqSet_closure {x : X} : IsLocallyClosedAt s x ↔
    s =ᶠ[𝓝 x] closure s :=
  (isLocallyClosedAt_tfae s x).out 1 6

@[deprecated (since := "2026-09-02")]
alias isLocallyClosedAt_iff_eventuallyEq_closure :=
  isLocallyClosedAt_iff_eventuallyEqSet_closure

lemma isLocallyClosedAt_iff_closure_eventuallySubset {x : X} : IsLocallyClosedAt s x ↔
    closure s ≤ᶠ[𝓝 x] s :=
  (isLocallyClosedAt_tfae s x).out 1 7

@[deprecated (since := "2026-09-02")]
alias isLocallyClosedAt_iff_closure_eventuallyLE :=
  isLocallyClosedAt_iff_closure_eventuallySubset

lemma isLocallyClosedAt_iff_coborder_mem_nhds {x : X} : IsLocallyClosedAt s x ↔ coborder s ∈ 𝓝 x :=
  (isLocallyClosedAt_tfae s x).out 1 9

lemma IsLocallyClosedAt.congr {x : X} (hs : IsLocallyClosedAt s x) (h : s =ᶠ[𝓝 x] t) :
    IsLocallyClosedAt t x := by
  rw [isLocallyClosedAt_iff_exists_isClosed_eventuallyEqSet] at *
  exact hs.imp fun _ ↦ And.imp_right <| h.symm.trans

lemma isLocallyClosedAt_congr {x : X} (h : s =ᶠ[𝓝 x] t) :
    IsLocallyClosedAt s x ↔ IsLocallyClosedAt t x :=
  ⟨fun hs ↦ hs.congr h, fun ht ↦ ht.congr h.symm⟩

lemma interior_coborder : interior (coborder s) = {x | IsLocallyClosedAt s x} := by
  ext
  simp [isLocallyClosedAt_iff_coborder_mem_nhds, mem_interior_iff_mem_nhds]

lemma IsLocallyClosedAt.inter {x : X} (hs : IsLocallyClosedAt s x) (ht : IsLocallyClosedAt t x) :
    IsLocallyClosedAt (s ∩ t) x := by
  rw [isLocallyClosedAt_iff_exists_isClosed_eventuallyEqSet] at *
  obtain ⟨Z₁, hZ₁, eq₁⟩ := hs
  obtain ⟨Z₂, hZ₂, eq₂⟩ := ht
  exact ⟨Z₁ ∩ Z₂, hZ₁.inter hZ₂, eq₁.inter eq₂⟩

lemma IsLocallyClosedAt.union {x : X} (hs : IsLocallyClosedAt s x) (ht : IsLocallyClosedAt t x) :
    IsLocallyClosedAt (s ∪ t) x := by
  rw [isLocallyClosedAt_iff_exists_isClosed_eventuallyEqSet] at *
  obtain ⟨Z₁, hZ₁, eq₁⟩ := hs
  obtain ⟨Z₂, hZ₂, eq₂⟩ := ht
  exact ⟨Z₁ ∪ Z₂, hZ₁.union hZ₂, eq₁.union eq₂⟩

end IsLocallyClosedAt

section IsLocallyClosed

lemma IsLocallyClosed.isLocallyClosedAt (hs : IsLocallyClosed s) {x : X} (hx : x ∈ s) :
    IsLocallyClosedAt s x := by
  obtain ⟨U, Z, U_open, Z_closed, s_eq⟩ := hs
  exact ⟨U, U_open.mem_nhds (s_eq ▸ hx).1, Z, Z_closed, by simp [s_eq]⟩

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
3. It is locally closed at each point of its coborder.
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
    simp [isOpen_iff_mem_nhds, isLocallyClosedAt_iff_coborder_mem_nhds]
  tfae_have 4 → 5 := fun H ↦ ⟨coborder s, H, by rw [coborder_inter_closure]⟩
  tfae_have 5 → 1 := fun ⟨U, U_open, eq⟩ ↦ ⟨U, closure s, U_open, isClosed_closure, eq⟩
  tfae_have 5 ↔ 6 := by
    simp [IsInducing.subtypeVal.isOpen_iff, Subtype.preimage_val_eq_preimage_val_iff,
      inter_eq_right.mpr subset_closure, inter_comm, eq_comm]
  tfae_finish

lemma isLocallyClosed_iff_isLocallyClosedAt :
    IsLocallyClosed s ↔ ∀ x ∈ s, IsLocallyClosedAt s x :=
  (isLocallyClosed_tfae s).out 1 2

lemma isLocallyClosed_iff_isOpen_coborder : IsLocallyClosed s ↔ IsOpen (coborder s) :=
  (isLocallyClosed_tfae s).out 1 4

alias ⟨IsLocallyClosed.isOpen_coborder, _⟩ := isLocallyClosed_iff_isOpen_coborder

lemma isLocallyClosed_iff_isOpen_preimage_val_closure :
    IsLocallyClosed s ↔ IsOpen (closure s ↓∩ s) :=
  (isLocallyClosed_tfae s).out 1 6

alias ⟨IsLocallyClosed.isOpen_preimage_val_closure, _⟩ :=
  isLocallyClosed_iff_isOpen_preimage_val_closure

end IsLocallyClosed
