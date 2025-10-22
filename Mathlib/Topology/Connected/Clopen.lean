/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Data.Set.Subset
import Mathlib.Data.Fintype.Sum
import Mathlib.Topology.Clopen
import Mathlib.Topology.Connected.Basic

/-!
# Connected subsets and their relation to clopen sets

In this file we show how connected subsets of a topological space are intimately connected
to clopen sets.

## Main declarations

+ `IsClopen.biUnion_connectedComponent_eq`: a clopen set is the union of its connected components.
+ `PreconnectedSpace.induction₂`: an induction principle for preconnected spaces.
+ `ConnectedComponents`: The connected components of a topological space, as a quotient type.

-/

open Set Function Topology TopologicalSpace Relation

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem IsPreconnected.subset_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t)
    (hne : (s ∩ t).Nonempty) : s ⊆ t :=
  hs.subset_left_of_subset_union ht.isOpen ht.compl.isOpen disjoint_compl_right (by simp) hne

theorem Sigma.isConnected_iff [∀ i, TopologicalSpace (X i)] {s : Set (Σ i, X i)} :
    IsConnected s ↔ ∃ i t, IsConnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s ⊆ range (Sigma.mk i) :=
      hs.isPreconnected.subset_isClopen isClopen_range_sigmaMk ⟨⟨i, x⟩, hx, x, rfl⟩
    exact ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_isOpenMap sigma_mk_injective isOpenMap_sigmaMk this,
      (Set.image_preimage_eq_of_subset this).symm⟩
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

theorem Sigma.isPreconnected_iff [hι : Nonempty ι] [∀ i, TopologicalSpace (X i)]
    {s : Set (Σ i, X i)} : IsPreconnected s ↔ ∃ i t, IsPreconnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
      exact ⟨a, t, ht.isPreconnected, rfl⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

theorem Sum.isConnected_iff [TopologicalSpace β] {s : Set (α ⊕ β)} :
    IsConnected s ↔
      (∃ t, IsConnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsConnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h : s ⊆ range Sum.inl :=
        hs.isPreconnected.subset_isClopen isClopen_range_inl ⟨.inl x, hx, x, rfl⟩
      refine Or.inl ⟨Sum.inl ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inl_injective isOpenMap_inl h
      · exact (image_preimage_eq_of_subset h).symm
    · have h : s ⊆ range Sum.inr :=
        hs.isPreconnected.subset_isClopen isClopen_range_inr ⟨.inr x, hx, x, rfl⟩
      refine Or.inr ⟨Sum.inr ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inr_injective isOpenMap_inr h
      · exact (image_preimage_eq_of_subset h).symm
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

theorem Sum.isPreconnected_iff [TopologicalSpace β] {s : Set (α ⊕ β)} :
    IsPreconnected s ↔
      (∃ t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsPreconnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isConnected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.isPreconnected, rfl⟩
    · exact Or.inr ⟨t, ht.isPreconnected, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

/-- A continuous map from a connected space to a disjoint union `Σ i, X i` can be lifted to one of
the components `X i`. See also `ContinuousMap.exists_lift_sigma` for a version with bundled
`ContinuousMap`s. -/
theorem Continuous.exists_lift_sigma [ConnectedSpace α] [∀ i, TopologicalSpace (X i)]
    {f : α → Σ i, X i} (hf : Continuous f) :
    ∃ (i : ι) (g : α → X i), Continuous g ∧ f = Sigma.mk i ∘ g := by
  obtain ⟨i, hi⟩ : ∃ i, range f ⊆ range (.mk i) := by
    rcases Sigma.isConnected_iff.1 (isConnected_range hf) with ⟨i, s, -, hs⟩
    exact ⟨i, hs.trans_subset (image_subset_range _ _)⟩
  rcases range_subset_range_iff_exists_comp.1 hi with ⟨g, rfl⟩
  refine ⟨i, g, ?_, rfl⟩
  rwa [← IsEmbedding.sigmaMk.continuous_iff] at hf

theorem nonempty_inter [PreconnectedSpace α] {s t : Set α} :
    IsOpen s → IsOpen t → s ∪ t = univ → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.isPreconnected_univ α _ _ s t

theorem isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = univ :=
  ⟨fun hs =>
    by_contradiction fun h =>
      have h1 : s ≠ ∅ ∧ sᶜ ≠ ∅ :=
        ⟨mt Or.inl h,
          mt (fun h2 => Or.inr <| (by rw [← compl_compl s, h2, compl_empty] : s = univ)) h⟩
      let ⟨_, h2, h3⟩ :=
        nonempty_inter hs.2 hs.1.isOpen_compl (union_compl_self s) (nonempty_iff_ne_empty.2 h1.1)
          (nonempty_iff_ne_empty.2 h1.2)
      h3 h2,
    by rintro (rfl | rfl) <;> [exact isClopen_empty; exact isClopen_univ]⟩

theorem IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h' : IsClopen s) (h : s.Nonempty) :
    s = univ :=
  (isClopen_iff.mp h').resolve_left h.ne_empty

open Set.Notation in
lemma isClopen_preimage_val {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsOpen u) (huv : Disjoint (frontier u) v) : IsClopen (v ↓∩ u) := by
  refine ⟨?_, isOpen_induced hu (f := Subtype.val)⟩
  refine isClosed_induced_iff.mpr ⟨closure u, isClosed_closure, ?_⟩
  apply image_val_injective
  simp only [Subtype.image_preimage_coe]
  rw [closure_eq_self_union_frontier, inter_union_distrib_left, inter_comm _ (frontier u),
    huv.inter_eq, union_empty]

section disjoint_subsets

variable [PreconnectedSpace α]
  {s : ι → Set α} (h_nonempty : ∀ i, (s i).Nonempty) (h_disj : Pairwise (Disjoint on s))
include h_nonempty h_disj

/-- In a preconnected space, any disjoint family of non-empty clopen subsets has at most one
element. -/
lemma subsingleton_of_disjoint_isClopen
    (h_clopen : ∀ i, IsClopen (s i)) :
    Subsingleton ι := by
  replace h_nonempty : ∀ i, s i ≠ ∅ := by intro i; rw [← nonempty_iff_ne_empty]; exact h_nonempty i
  rw [← not_nontrivial_iff_subsingleton]
  by_contra contra
  obtain ⟨i, j, h_ne⟩ := contra
  replace h_ne : s i ∩ s j = ∅ := by
    simpa only [← bot_eq_empty, eq_bot_iff, ← inf_eq_inter, ← disjoint_iff_inf_le] using h_disj h_ne
  rcases isClopen_iff.mp (h_clopen i) with hi | hi
  · exact h_nonempty i hi
  · rw [hi, univ_inter] at h_ne
    exact h_nonempty j h_ne

/-- In a preconnected space, any disjoint cover by non-empty open subsets has at most one
element. -/
lemma subsingleton_of_disjoint_isOpen_iUnion_eq_univ
    (h_open : ∀ i, IsOpen (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i ↦ ⟨?_, h_open i⟩)
  rw [← isOpen_compl_iff, compl_eq_univ_diff, ← h_Union, iUnion_diff]
  refine isOpen_iUnion (fun j ↦ ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_open j

/-- In a preconnected space, any finite disjoint cover by non-empty closed subsets has at most one
element. -/
lemma subsingleton_of_disjoint_isClosed_iUnion_eq_univ [Finite ι]
    (h_closed : ∀ i, IsClosed (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i ↦ ⟨h_closed i, ?_⟩)
  rw [← isClosed_compl_iff, compl_eq_univ_diff, ← h_Union, iUnion_diff]
  refine isClosed_iUnion_of_finite (fun j ↦ ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_closed j

end disjoint_subsets

theorem frontier_eq_empty_iff [PreconnectedSpace α] {s : Set α} :
    frontier s = ∅ ↔ s = ∅ ∨ s = univ :=
  isClopen_iff_frontier_eq_empty.symm.trans isClopen_iff

theorem nonempty_frontier_iff [PreconnectedSpace α] {s : Set α} :
    (frontier s).Nonempty ↔ s.Nonempty ∧ s ≠ univ := by
  simp only [nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff, not_or]

/-- In a preconnected space, given a transitive relation `P`, if `P x y` and `P y x` are true
for `y` close enough to `x`, then `P x y` holds for all `x, y`. This is a version of the fact
that, if an equivalence relation has open classes, then it has a single equivalence class. -/
lemma PreconnectedSpace.induction₂' [PreconnectedSpace α] (P : α → α → Prop)
    (h : ∀ x, ∀ᶠ y in 𝓝 x, P x y ∧ P y x) (h' : Transitive P) (x y : α) :
    P x y := by
  let u := {z | P x z}
  have A : IsClosed u := by
    apply isClosed_iff_nhds.2 (fun z hz ↦ ?_)
    rcases hz _ (h z) with ⟨t, ht, h't⟩
    exact h' h't ht.2
  have B : IsOpen u := by
    apply isOpen_iff_mem_nhds.2 (fun z hz ↦ ?_)
    filter_upwards [h z] with t ht
    exact h' hz ht.1
  have C : u.Nonempty := ⟨x, (mem_of_mem_nhds (h x)).1⟩
  have D : u = Set.univ := IsClopen.eq_univ ⟨A, B⟩ C
  change y ∈ u
  simp [D]

/-- In a preconnected space, if a symmetric transitive relation `P x y` is true for `y` close
enough to `x`, then it holds for all `x, y`. This is a version of the fact that, if an equivalence
relation has open classes, then it has a single equivalence class. -/
lemma PreconnectedSpace.induction₂ [PreconnectedSpace α] (P : α → α → Prop)
    (h : ∀ x, ∀ᶠ y in 𝓝 x, P x y) (h' : Transitive P) (h'' : Symmetric P) (x y : α) :
    P x y := by
  refine PreconnectedSpace.induction₂' P (fun z ↦ ?_) h' x y
  filter_upwards [h z] with a ha
  exact ⟨ha, h'' ha⟩

/-- In a preconnected set, given a transitive relation `P`, if `P x y` and `P y x` are true
for `y` close enough to `x`, then `P x y` holds for all `x, y`. This is a version of the fact
that, if an equivalence relation has open classes, then it has a single equivalence class. -/
lemma IsPreconnected.induction₂' {s : Set α} (hs : IsPreconnected s) (P : α → α → Prop)
    (h : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, P x y ∧ P y x)
    (h' : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → P x y → P y z → P x z)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : P x y := by
  let Q : s → s → Prop := fun a b ↦ P a b
  change Q ⟨x, hx⟩ ⟨y, hy⟩
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  apply PreconnectedSpace.induction₂'
  · rintro ⟨x, hx⟩
    have Z := h x hx
    rwa [nhdsWithin_eq_map_subtype_coe] at Z
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hab hbc
    exact h' a b c ha hb hc hab hbc

/-- In a preconnected set, if a symmetric transitive relation `P x y` is true for `y` close
enough to `x`, then it holds for all `x, y`. This is a version of the fact that, if an equivalence
relation has open classes, then it has a single equivalence class. -/
lemma IsPreconnected.induction₂ {s : Set α} (hs : IsPreconnected s) (P : α → α → Prop)
    (h : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, P x y)
    (h' : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → P x y → P y z → P x z)
    (h'' : ∀ x y, x ∈ s → y ∈ s → P x y → P y x)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : P x y := by
  apply hs.induction₂' P (fun z hz ↦ ?_) h' hx hy
  filter_upwards [h z hz, self_mem_nhdsWithin] with a ha h'a
  exact ⟨ha, h'' z a hz h'a ha⟩

/-- A set `s` is preconnected if and only if for every cover by two open sets that are disjoint on
`s`, it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_disjoint {s : Set α} :
    IsPreconnected s ↔
      ∀ u v, IsOpen u → IsOpen v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
theorem isConnected_iff_sUnion_disjoint_open {s : Set α} :
    IsConnected s ↔
      ∀ U : Finset (Set α), (∀ u v : Set α, u ∈ U → v ∈ U → (s ∩ (u ∩ v)).Nonempty → u = v) →
        (∀ u ∈ U, IsOpen u) → (s ⊆ ⋃₀ ↑U) → ∃ u ∈ U, s ⊆ u := by
  rw [IsConnected, isPreconnected_iff_subset_of_disjoint]
  classical
  refine ⟨fun ⟨hne, h⟩ U hU hUo hsU => ?_, fun h => ⟨?_, fun u v hu hv hs hsuv => ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => exact absurd (by simpa using hsU) hne.not_subset_empty
    | insert u U uU IH =>
      simp only [← forall_cond_comm, Finset.forall_mem_insert, Finset.exists_mem_insert,
        Finset.coe_insert, sUnion_insert, implies_true, true_and] at *
      refine (h _ hUo.1 (⋃₀ ↑U) (isOpen_sUnion hUo.2) hsU ?_).imp_right ?_
      · refine subset_empty_iff.1 fun x ⟨hxs, hxu, v, hvU, hxv⟩ => ?_
        exact ne_of_mem_of_not_mem hvU uU (hU.1 v hvU ⟨x, hxs, hxu, hxv⟩).symm
      · exact IH (fun u hu => (hU.2 u hu).2) hUo.2
  · simpa [subset_empty_iff, nonempty_iff_ne_empty] using h ∅
  · rw [← not_nonempty_iff_eq_empty] at hsuv
    have := hsuv; rw [inter_comm u] at this
    simpa [*, or_imp, forall_and] using h {u, v}

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem disjoint_or_subset_of_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t) :
    Disjoint s t ∨ s ⊆ t :=
  (disjoint_or_nonempty_inter s t).imp_right <| hs.subset_isClopen ht

/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_disjoint_closed :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [isPreconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · rw [isPreconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

/-- A closed set `s` is preconnected if and only if for every cover by two closed sets that are
disjoint, it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → Disjoint u v → s ⊆ u ∨ s ⊆ v := by
  refine isPreconnected_iff_subset_of_disjoint_closed.trans ⟨?_, ?_⟩ <;> intro H u v hu hv hss huv
  · apply H u v hu hv hss
    rw [huv.inter_eq, inter_empty]
  have H1 := H (u ∩ s) (v ∩ s)
  rw [subset_inter_iff, subset_inter_iff] at H1
  simp only [Subset.refl, and_true] at H1
  apply H1 (hu.inter hs) (hv.inter hs)
  · rw [← union_inter_distrib_right]
    exact subset_inter hss Subset.rfl
  · rwa [disjoint_iff_inter_eq_empty, ← inter_inter_distrib_right, inter_comm]

theorem IsClopen.connectedComponent_subset {x} (hs : IsClopen s) (hx : x ∈ s) :
    connectedComponent x ⊆ s :=
  isPreconnected_connectedComponent.subset_isClopen hs ⟨x, mem_connectedComponent, hx⟩

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
theorem connectedComponent_subset_iInter_isClopen {x : α} :
    connectedComponent x ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z :=
  subset_iInter fun Z => Z.2.1.connectedComponent_subset Z.2.2

/-- A clopen set is the union of its connected components. -/
theorem IsClopen.biUnion_connectedComponent_eq {Z : Set α} (h : IsClopen Z) :
    ⋃ x ∈ Z, connectedComponent x = Z :=
  Subset.antisymm (iUnion₂_subset fun _ => h.connectedComponent_subset) fun _ h =>
    mem_iUnion₂_of_mem h mem_connectedComponent

open Set.Notation in
/-- If `u v : Set X` and `u ⊆ v` is clopen in `v`, then `u` is the union of the connected
components of `v` in `X` which intersect `u`. -/
lemma IsClopen.biUnion_connectedComponentIn {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsClopen (v ↓∩ u)) (huv₁ : u ⊆ v) :
    u = ⋃ x ∈ u, connectedComponentIn v x := by
  have := congr(((↑) : Set v → Set X) $(hu.biUnion_connectedComponent_eq.symm))
  simp only [Subtype.image_preimage_coe, mem_preimage, iUnion_coe_set, image_val_iUnion,
    inter_eq_right.mpr huv₁] at this
  nth_rw 1 [this]
  congr! 2 with x hx
  simp only [← connectedComponentIn_eq_image]
  exact le_antisymm (iUnion_subset fun _ ↦ le_rfl) <|
    iUnion_subset fun hx ↦ subset_iUnion₂_of_subset (huv₁ hx) hx le_rfl

lemma IsClopen.connectedComponentIn_eq {U : Set α} (hU : IsClopen U) {x : α} (hx : x ∈ U) :
    connectedComponentIn U x = connectedComponent x :=
  subset_antisymm ((isPreconnected_connectedComponentIn).subset_connectedComponent
    (mem_connectedComponentIn hx)) <|
    (isPreconnected_connectedComponent).subset_connectedComponentIn (mem_connectedComponent)
    (hU.connectedComponent_subset hx)

variable [TopologicalSpace β] {f : α → β}

/-- The preimage of a connected component is preconnected if the function has connected fibers
and a subset is closed iff the preimage is. -/
theorem preimage_connectedComponent_connected
    (connected_fibers : ∀ t : β, IsConnected (f ⁻¹' {t}))
    (hcl : ∀ T : Set β, IsClosed T ↔ IsClosed (f ⁻¹' T)) (t : β) :
    IsConnected (f ⁻¹' connectedComponent t) := by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage connectedComponent_nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' connectedComponent t) :=
    (hcl (connectedComponent t)).1 isClosed_connectedComponent
  -- To show it's preconnected we decompose (f ⁻¹' connectedComponent t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose connectedComponent t into T₁ and T₂
  -- we will show that connectedComponent t is a subset of either and hence
  -- (f ⁻¹' connectedComponent t) is a subset of u or v
  let T₁ := { t' ∈ connectedComponent t | f ⁻¹' {t'} ⊆ u }
  let T₂ := { t' ∈ connectedComponent t | f ⁻¹' {t'} ⊆ v }
  have fiber_decomp : ∀ t' ∈ connectedComponent t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq, inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' connectedComponent t ∩ u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' connectedComponent t ∩ v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover connectedComponent t and are disjoint.
  have hT₁ : IsClosed T₁ := (hcl T₁).2 (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := (hcl T₂).2 (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : connectedComponent t ⊆ T₁ ∪ T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    rcases fiber_decomp t' ht' with htu | htv
    · left; exact ⟨ht', htu⟩
    · right; exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine Disjoint.of_preimage hf ?_
    rw [T₁_u, T₂_v, disjoint_iff_inter_eq_empty, ← inter_inter_distrib_left, uv_disj.inter_eq,
      inter_empty]
  -- Now we do cases on whether (connectedComponent t) is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_connectedComponent).1
    isPreconnected_connectedComponent T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h | h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' connectedComponent t ⊆ f ⁻¹' T₁
      from (this.trans T₁_u.1).trans inter_subset_right
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' connectedComponent t ⊆ f ⁻¹' T₂
      from (this.trans T₂_v.1).trans inter_subset_right
    exact preimage_mono h

theorem Topology.IsQuotientMap.preimage_connectedComponent (hf : IsQuotientMap f)
    (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f ⁻¹' connectedComponent (f a) = connectedComponent a :=
  ((preimage_connectedComponent_connected h_fibers (fun _ => hf.isClosed_preimage.symm)
      _).subset_connectedComponent mem_connectedComponent).antisymm
    (hf.continuous.mapsTo_connectedComponent a)

lemma Topology.IsQuotientMap.image_connectedComponent {f : α → β} (hf : IsQuotientMap f)
    (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f '' connectedComponent a = connectedComponent (f a) := by
  rw [← hf.preimage_connectedComponent h_fibers, image_preimage_eq _ hf.surjective]

end Preconnected

section connectedComponentSetoid
/-- The setoid of connected components of a topological space -/
def connectedComponentSetoid (α : Type*) [TopologicalSpace α] : Setoid α :=
  ⟨fun x y => connectedComponent x = connectedComponent y,
    ⟨fun x => by trivial, fun h1 => h1.symm, fun h1 h2 => h1.trans h2⟩⟩

/-- The quotient of a space by its connected components -/
def ConnectedComponents (α : Type u) [TopologicalSpace α] :=
  Quotient (connectedComponentSetoid α)

namespace ConnectedComponents

/-- Coercion from a topological space to the set of connected components of this space. -/
def mk : α → ConnectedComponents α := Quotient.mk''

instance : CoeTC α (ConnectedComponents α) := ⟨mk⟩

@[simp]
theorem coe_eq_coe {x y : α} :
    (x : ConnectedComponents α) = y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''

theorem coe_ne_coe {x y : α} :
    (x : ConnectedComponents α) ≠ y ↔ connectedComponent x ≠ connectedComponent y :=
  coe_eq_coe.not

theorem coe_eq_coe' {x y : α} : (x : ConnectedComponents α) = y ↔ x ∈ connectedComponent y :=
  coe_eq_coe.trans connectedComponent_eq_iff_mem

instance [Inhabited α] : Inhabited (ConnectedComponents α) :=
  ⟨mk default⟩

instance : TopologicalSpace (ConnectedComponents α) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

theorem surjective_coe : Surjective (mk : α → ConnectedComponents α) :=
  Quot.mk_surjective

theorem isQuotientMap_coe : IsQuotientMap (mk : α → ConnectedComponents α) :=
  isQuotientMap_quot_mk

@[continuity]
theorem continuous_coe : Continuous (mk : α → ConnectedComponents α) :=
  isQuotientMap_coe.continuous

@[simp]
theorem range_coe : range (mk : α → ConnectedComponents α) = univ :=
  surjective_coe.range_eq

lemma nonempty_iff_nonempty : Nonempty (ConnectedComponents α) ↔ Nonempty α :=
  ⟨fun _ ↦ ConnectedComponents.surjective_coe.nonempty, fun h ↦ h.map ConnectedComponents.mk⟩

instance [Nonempty α] : Nonempty (ConnectedComponents α) := by
  rwa [ConnectedComponents.nonempty_iff_nonempty]

lemma isEmpty_iff_isEmpty : IsEmpty (ConnectedComponents α) ↔ IsEmpty α := by
  rw [← not_iff_not, not_isEmpty_iff, not_isEmpty_iff, nonempty_iff_nonempty]

instance subsingleton [PreconnectedSpace α] : Subsingleton (ConnectedComponents α) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := surjective_coe x
  obtain ⟨y, rfl⟩ := surjective_coe y
  simp_rw [coe_eq_coe, PreconnectedSpace.connectedComponent_eq_univ, ]

section

variable {ι : Type*} {U : ι → Set α} (hclopen : ∀ i, IsClopen (U i))
  (hdisj : Pairwise (Disjoint on U)) (hunion : ⋃ i, U i = Set.univ)
  (hconn : ∀ i, IsPreconnected (U i))

include hclopen hdisj hunion in
/-- A pairwise disjoint cover by clopens partitions the connected components. -/
noncomputable def equivOfIsClopen : ConnectedComponents α ≃ Σ i, ConnectedComponents (U i) := by
  haveI heq {x : α} {i} (hx : x ∈ U i) :
      Subtype.val '' connectedComponent ⟨x, hx⟩ = connectedComponent x := by
    rw [← connectedComponentIn_eq_image hx, (hclopen i).connectedComponentIn_eq hx]
  refine .symm <| .ofBijective
    (fun ⟨i, x⟩ ↦
      Quotient.lift (ConnectedComponents.mk ∘ Subtype.val)
        (fun x y (hxy : connectedComponent x = connectedComponent y) ↦ by
          simp [← heq x.2, ← heq y.2, hxy])
        x)
    ⟨fun ⟨i, x⟩ ⟨j, y⟩ hxy ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hunion x
    simp only [Sigma.exists]
    use i, .mk ⟨x, hi⟩
    rfl
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    replace hxy : ConnectedComponents.mk x.val = ConnectedComponents.mk y.val := hxy
    rw [ConnectedComponents.coe_eq_coe] at hxy
    obtain rfl : i = j := by
      apply hdisj.eq
      rw [Set.not_disjoint_iff]
      exact ⟨x, x.2, (hclopen j).connectedComponent_subset y.2 (hxy ▸ mem_connectedComponent)⟩
    simp [← Set.image_val_inj, heq, hxy]

include hclopen hdisj hunion in
/-- If `ι` indexes a disjoint union decomposition of `α`, it is equivalent to the connected
components of `α`. -/
noncomputable def equivOfIsClopenOfIsConnected (hconn : ∀ i, IsConnected (U i)) :
    ConnectedComponents α ≃ ι :=
  have _ (i) : ConnectedSpace (U i) := isConnected_iff_connectedSpace.mp (hconn i)
  letI _ (i) : Unique (ConnectedComponents <| U i) := (nonempty_unique _).some
  (equivOfIsClopen hclopen hdisj hunion).trans (.sigmaUnique _ _)

end

variable (α) in
open Set in
/-- If `X` has infinitely many connected components, it admits disjoint union decompositions with
arbitrarily many summands. -/
lemma exists_fun_isClopen_of_infinite [Infinite (ConnectedComponents α)] (n : ℕ) (hn : 0 < n) :
    ∃ (U : Fin n → Set α), (∀ i, IsClopen (U i)) ∧ (∀ i, (U i).Nonempty) ∧
      Pairwise (Function.onFun Disjoint U) ∧ ⋃ i, U i = Set.univ :=
  suffices h : ∃ (ι : Type) (e : ι ≃ Fin n) (U : ι → Set α), (∀ i, IsClopen (U i)) ∧
      (∀ i, (U i).Nonempty) ∧ Pairwise (Function.onFun Disjoint U) ∧ ⋃ i, U i = Set.univ by
    obtain ⟨ι, e, U, hU1, hU2, hU3, hU4⟩ := h
    refine ⟨U ∘ e.symm, fun i ↦ hU1 _, fun i ↦ hU2 _,
      fun i j h ↦ hU3 <| e.symm.injective.ne_iff.mpr h, iUnion_eq_univ_iff.mpr fun x ↦ ?_⟩
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hU4 x
    exact ⟨e i, by simp [hi]⟩
  have : Nonempty α := ConnectedComponents.nonempty_iff_nonempty.mp inferInstance
  match n with
  | 1 => ⟨Unit, Fintype.equivFinOfCardEq rfl, fun _ ↦ Set.univ, by simp [isClopen_univ],
    by simp, Subsingleton.pairwise, by simp [Set.iUnion_const]⟩
  | n + 2 => by
    obtain ⟨U, hU₁, hU₂, hU₃, hU₄⟩ := exists_fun_isClopen_of_infinite (n + 1) (by simp)
    obtain ⟨i, hi⟩ : ∃ (i : Fin (n + 1)), ¬ IsPreconnected (U i) := by
      by_contra! h
      exact Infinite.not_finite <|
        .of_equiv _ (equivOfIsClopenOfIsConnected hU₁ hU₃ hU₄ fun i ↦ ⟨hU₂ i, h i⟩).symm
    simp only [IsPreconnected, not_forall] at hi
    obtain ⟨V, W, hV, hW, hle, hVU, hWU, h⟩ := hi
    rw [Set.not_nonempty_iff_eq_empty, ← Set.inter_assoc] at h
    have hunion : V ∩ U i ∪ W ∩ U i = U i := by rwa [← union_inter_distrib_right, inter_eq_right]
    refine ⟨{ x : Fin (n + 1) // x ≠ i } ⊕ Unit ⊕ Unit, Fintype.equivFinOfCardEq (by simp),
        Sum.elim (fun j ↦ U j) (Sum.elim (fun _ ↦ V ∩ U i) fun _ ↦ W ∩ U i), ?_, ?_, ?_, ?_⟩
    · rintro (x|-|-)
      · exact hU₁ _
      all_goals simp only [ne_eq, Sum.elim_inr, Sum.elim_inl]; rw [Set.inter_comm]
      · exact isClopen_inter_of_disjoint_cover_clopen' (hU₁ _) hle hV hW h
      · refine isClopen_inter_of_disjoint_cover_clopen' (hU₁ _) (union_comm _ _ ▸ hle) hW hV ?_
        rwa [Set.inter_assoc, Set.inter_comm W V, ← Set.inter_assoc]
    · rintro (x|x|x)
      · exact hU₂ _
      · rwa [Sum.elim_inr, Sum.elim_inl, Set.inter_comm]
      · rwa [Sum.elim_inr, Sum.elim_inr, Set.inter_comm]
    · rintro (x|x|x) (y|y|y) hxy
      · exact hU₃ fun hxy' ↦ hxy (congrArg Sum.inl <| Subtype.ext_iff.mpr hxy')
      · exact Disjoint.inter_right' _ (hU₃ x.2)
      · exact Disjoint.inter_right' _ (hU₃ x.2)
      · exact Disjoint.inter_left' _ (hU₃ <| Ne.symm y.2)
      · contradiction
      · exact Disjoint.inter_right _ (disjoint_iff_inter_eq_empty.mpr <| inter_comm V (U i) ▸ h)
      · exact Disjoint.inter_left' _ (hU₃ <| Ne.symm y.2)
      · apply Disjoint.inter_right _ (disjoint_iff_inter_eq_empty.mpr ?_)
        rwa [Sum.elim_inr, Sum.elim_inr, inter_comm W, inter_assoc, inter_comm W V, ← inter_assoc]
      · contradiction
    · simp only [iUnion_sumElim, iUnion_const, hunion, eq_univ_iff_forall, mem_union, mem_iUnion]
      intro x
      obtain ⟨j, hj⟩ := (Set.iUnion_eq_univ_iff.mp hU₄) x
      by_cases h : j = i
      · exact h ▸ Or.inr hj
      · exact Or.inl ⟨⟨j, h⟩, hj⟩

end ConnectedComponents

/-- The preimage of a singleton in `connectedComponents` is the connected component
of an element in the equivalence class. -/
theorem connectedComponents_preimage_singleton {x : α} :
    (↑) ⁻¹' ({↑x} : Set (ConnectedComponents α)) = connectedComponent x := by
  ext y
  rw [mem_preimage, mem_singleton_iff, ConnectedComponents.coe_eq_coe']

/-- The preimage of the image of a set under the quotient map to `connectedComponents α`
is the union of the connected components of the elements in it. -/
theorem connectedComponents_preimage_image (U : Set α) :
    (↑) ⁻¹' ((↑) '' U : Set (ConnectedComponents α)) = ⋃ x ∈ U, connectedComponent x := by
  simp only [connectedComponents_preimage_singleton, preimage_iUnion₂, image_eq_iUnion]

lemma ConnectedComponents.discreteTopology_iff :
    DiscreteTopology (ConnectedComponents α) ↔ ∀ x : α, IsOpen (connectedComponent x) := by
  simp_rw [← singletons_open_iff_discrete, ← connectedComponents_preimage_singleton,
    isQuotientMap_coe.isOpen_preimage, surjective_coe.forall]

end connectedComponentSetoid

/-- If every map to `Bool` (a discrete two-element space), that is
continuous on a set `s`, is constant on s, then s is preconnected -/
theorem isPreconnected_of_forall_constant {s : Set α}
    (hs : ∀ f : α → Bool, ContinuousOn f s → ∀ x ∈ s, ∀ y ∈ s, f x = f y) : IsPreconnected s := by
  unfold IsPreconnected
  by_contra!
  rcases this with ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩
  have hy : y ∉ u := fun y_in_u => eq_empty_iff_forall_notMem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩
  have : ContinuousOn u.boolIndicator s := by
    apply (continuousOn_boolIndicator_iff_isClopen _ _).mpr ⟨_, _⟩
    · rw [preimage_subtype_coe_eq_compl hsuv H]
      exact (v_op.preimage continuous_subtype_val).isClosed_compl
    · exact u_op.preimage continuous_subtype_val
  simpa [(u.mem_iff_boolIndicator _).mp x_in_u, (u.notMem_iff_boolIndicator _).mp hy] using
    hs _ this x x_in_s y y_in_s

/-- A `PreconnectedSpace` version of `isPreconnected_of_forall_constant` -/
theorem preconnectedSpace_of_forall_constant
    (hs : ∀ f : α → Bool, Continuous f → ∀ x y, f x = f y) : PreconnectedSpace α :=
  ⟨isPreconnected_of_forall_constant fun f hf x _ y _ =>
      hs f (continuousOn_univ.mp hf) x y⟩

theorem preconnectedSpace_iff_clopen :
    PreconnectedSpace α ↔ ∀ s : Set α, IsClopen s → s = ∅ ∨ s = Set.univ := by
  refine ⟨fun _ _ => isClopen_iff.mp, fun h ↦ ?_⟩
  refine preconnectedSpace_of_forall_constant fun f hf x y ↦ ?_
  have : f ⁻¹' {false} = (f ⁻¹' {true})ᶜ := by
    rw [← Set.preimage_compl, Bool.compl_singleton, Bool.not_true]
  obtain (h | h) := h _ ((isClopen_discrete {true}).preimage hf) <;> simp_all

theorem connectedSpace_iff_clopen :
    ConnectedSpace α ↔ Nonempty α ∧ ∀ s : Set α, IsClopen s → s = ∅ ∨ s = Set.univ := by
  rw [connectedSpace_iff_univ, IsConnected, ← preconnectedSpace_iff_univ,
    preconnectedSpace_iff_clopen, Set.nonempty_iff_univ_nonempty]
