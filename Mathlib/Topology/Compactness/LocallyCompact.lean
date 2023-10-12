/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Compactness.Compact
/-!
# Locally compact spaces

We define the following classes of topological spaces:
* `WeaklyLocallyCompactSpace`: every point `x` has a compact neighborhood.
* `LocallyCompactSpace`: for every point `x`, every open neighborhood of `x` contains a compact
  neighborhood of `x`. The definition is formulated in terms of the neighborhood filter.
-/
open Set Filter Topology TopologicalSpace Classical

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {π : ι → Type*}

variable [TopologicalSpace α] [TopologicalSpace β] {s t : Set α}


/-- We say that a topological space is a *weakly locally compact space*,
if each point of this space admits a compact neighborhood. -/
class WeaklyLocallyCompactSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- Every point of a weakly locally compact space admits a compact neighborhood. -/
  exists_compact_mem_nhds (x : α) : ∃ s, IsCompact s ∧ s ∈ 𝓝 x

export WeaklyLocallyCompactSpace (exists_compact_mem_nhds)
#align exists_compact_mem_nhds WeaklyLocallyCompactSpace.exists_compact_mem_nhds

instance [WeaklyLocallyCompactSpace α] [WeaklyLocallyCompactSpace β] :
    WeaklyLocallyCompactSpace (α × β) where
  exists_compact_mem_nhds x :=
    let ⟨s₁, hc₁, h₁⟩ := exists_compact_mem_nhds x.1
    let ⟨s₂, hc₂, h₂⟩ := exists_compact_mem_nhds x.2
    ⟨s₁ ×ˢ s₂, hc₁.prod hc₂, prod_mem_nhds h₁ h₂⟩

instance {ι : Type*} [Finite ι] {X : ι → Type*} [(i : ι) → TopologicalSpace (X i)]
    [(i : ι) → WeaklyLocallyCompactSpace (X i)] :
    WeaklyLocallyCompactSpace ((i : ι) → X i) where
  exists_compact_mem_nhds := fun f ↦ by
    choose s hsc hs using fun i ↦ exists_compact_mem_nhds (f i)
    exact ⟨pi univ s, isCompact_univ_pi hsc, set_pi_mem_nhds univ.toFinite fun i _ ↦ hs i⟩

instance (priority := 100) [CompactSpace α] : WeaklyLocallyCompactSpace α where
  exists_compact_mem_nhds _ := ⟨univ, isCompact_univ, univ_mem⟩

/-- In a weakly locally compact space,
every compact set is contained in the interior of a compact set. -/
theorem exists_compact_superset [WeaklyLocallyCompactSpace α] {K : Set α} (hK : IsCompact K) :
    ∃ K', IsCompact K' ∧ K ⊆ interior K' := by
  choose s hc hmem using fun x : α ↦ exists_compact_mem_nhds x
  rcases hK.elim_nhds_subcover _ fun x _ ↦ interior_mem_nhds.2 (hmem x) with ⟨I, -, hIK⟩
  refine ⟨⋃ x ∈ I, s x, I.isCompact_biUnion fun _ _ ↦ hc _, hIK.trans ?_⟩
  exact iUnion₂_subset fun x hx ↦ interior_mono <| subset_iUnion₂ (s := fun x _ ↦ s x) x hx
#align exists_compact_superset exists_compact_superset

/-- In a weakly locally compact space,
the filters `𝓝 x` and `cocompact α` are disjoint for all `α`. -/
theorem disjoint_nhds_cocompact [WeaklyLocallyCompactSpace α] (x : α) :
    Disjoint (𝓝 x) (cocompact α) :=
  let ⟨_, hc, hx⟩ := exists_compact_mem_nhds x
  disjoint_of_disjoint_of_mem disjoint_compl_right hx hc.compl_mem_cocompact

/-- There are various definitions of "locally compact space" in the literature,
which agree for Hausdorff spaces but not in general.
This one is the precise condition on X needed
for the evaluation map `C(X, Y) × X → Y` to be continuous for all `Y`
when `C(X, Y)` is given the compact-open topology.

See also `WeaklyLocallyCompactSpace`, a typeclass that only assumes
that each point has a compact neighborhood. -/
class LocallyCompactSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- In a locally compact space,
    every neighbourhood of every point contains a compact neighbourhood of that same point. -/
  local_compact_nhds : ∀ (x : α), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s
#align locally_compact_space LocallyCompactSpace

theorem compact_basis_nhds [LocallyCompactSpace α] (x : α) :
    (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x ∧ IsCompact s) fun s => s :=
  hasBasis_self.2 <| by simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x
#align compact_basis_nhds compact_basis_nhds

theorem local_compact_nhds [LocallyCompactSpace α] {x : α} {n : Set α} (h : n ∈ 𝓝 x) :
    ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s :=
  LocallyCompactSpace.local_compact_nhds _ _ h
#align local_compact_nhds local_compact_nhds

theorem locallyCompactSpace_of_hasBasis {ι : α → Type*} {p : ∀ x, ι x → Prop}
    {s : ∀ x, ι x → Set α} (h : ∀ x, (𝓝 x).HasBasis (p x) (s x))
    (hc : ∀ x i, p x i → IsCompact (s x i)) : LocallyCompactSpace α :=
  ⟨fun x _t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩
#align locally_compact_space_of_has_basis locallyCompactSpace_of_hasBasis

instance Prod.locallyCompactSpace (α : Type*) (β : Type*) [TopologicalSpace α]
    [TopologicalSpace β] [LocallyCompactSpace α] [LocallyCompactSpace β] :
    LocallyCompactSpace (α × β) :=
  have := fun x : α × β => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
  locallyCompactSpace_of_hasBasis this fun _ _ ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂
#align prod.locally_compact_space Prod.locallyCompactSpace

section Pi

variable [∀ i, TopologicalSpace (π i)] [∀ i, LocallyCompactSpace (π i)]

/-- In general it suffices that all but finitely many of the spaces are compact,
  but that's not straightforward to state and use. -/
instance Pi.locallyCompactSpace_of_finite [Finite ι] : LocallyCompactSpace (∀ i, π i) :=
  ⟨fun t n hn => by
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨s, -, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine' ⟨(Set.univ : Set ι).pi n'', _, subset_trans (fun _ h => _) hsub, isCompact_univ_pi hc⟩
    · exact (set_pi_mem_nhds_iff (@Set.finite_univ ι _) _).mpr fun i _ => hn'' i
    · exact fun i _ => hsub' i (h i trivial)⟩
#align pi.locally_compact_space_of_finite Pi.locallyCompactSpace_of_finite

/-- For spaces that are not Hausdorff. -/
instance Pi.locallyCompactSpace [∀ i, CompactSpace (π i)] : LocallyCompactSpace (∀ i, π i) :=
  ⟨fun t n hn => by
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨s, hs, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine' ⟨s.pi n'', _, subset_trans (fun _ => _) hsub, _⟩
    · exact (set_pi_mem_nhds_iff hs _).mpr fun i _ => hn'' i
    · exact forall₂_imp fun i _ hi' => hsub' i hi'
    · rw [← Set.univ_pi_ite]
      refine' isCompact_univ_pi fun i => _
      by_cases h : i ∈ s
      · rw [if_pos h]
        exact hc i
      · rw [if_neg h]
        exact CompactSpace.isCompact_univ⟩
#align pi.locally_compact_space Pi.locallyCompactSpace

instance Function.locallyCompactSpace_of_finite [Finite ι] [LocallyCompactSpace β] :
    LocallyCompactSpace (ι → β) :=
  Pi.locallyCompactSpace_of_finite
#align function.locally_compact_space_of_finite Function.locallyCompactSpace_of_finite

instance Function.locallyCompactSpace [LocallyCompactSpace β] [CompactSpace β] :
    LocallyCompactSpace (ι → β) :=
  Pi.locallyCompactSpace
#align function.locally_compact_space Function.locallyCompactSpace

end Pi

/-- A reformulation of the definition of locally compact space: In a locally compact space,
  every open set containing `x` has a compact subset containing `x` in its interior. -/
theorem exists_compact_subset [LocallyCompactSpace α] {x : α} {U : Set α} (hU : IsOpen U)
    (hx : x ∈ U) : ∃ K : Set α, IsCompact K ∧ x ∈ interior K ∧ K ⊆ U := by
  rcases LocallyCompactSpace.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩
#align exists_compact_subset exists_compact_subset

instance (priority := 100) [LocallyCompactSpace α] : WeaklyLocallyCompactSpace α where
  exists_compact_mem_nhds (x : α) :=
    let ⟨K, hKc, hx, _⟩ := exists_compact_subset isOpen_univ (mem_univ x)
    ⟨K, hKc, mem_interior_iff_mem_nhds.1 hx⟩

/-- In a locally compact space, for every containment `K ⊆ U` of a compact set `K` in an open
  set `U`, there is a compact neighborhood `L` such that `K ⊆ L ⊆ U`: equivalently, there is a
  compact `L` such that `K ⊆ interior L` and `L ⊆ U`. -/
theorem exists_compact_between [hα : LocallyCompactSpace α] {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (h_KU : K ⊆ U) : ∃ L, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U := by
  choose V hVc hxV hKV using fun x : K => exists_compact_subset hU (h_KU x.2)
  have : K ⊆ ⋃ x, interior (V x) := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxV _⟩
  rcases hK.elim_finite_subcover _ (fun x => @isOpen_interior α _ (V x)) this with ⟨t, ht⟩
  refine'
    ⟨_, t.isCompact_biUnion fun x _ => hVc x, fun x hx => _, Set.iUnion₂_subset fun i _ => hKV i⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hy⟩
  exact interior_mono (subset_iUnion₂ y hyt) hy
#align exists_compact_between exists_compact_between

protected theorem ClosedEmbedding.locallyCompactSpace [LocallyCompactSpace β] {f : α → β}
    (hf : ClosedEmbedding f) : LocallyCompactSpace α :=
  haveI : ∀ x : α, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (f x) ∧ IsCompact s) fun s => f ⁻¹' s := by
    intro x
    rw [hf.toInducing.nhds_eq_comap]
    exact (compact_basis_nhds _).comap _
  locallyCompactSpace_of_hasBasis this fun x s hs => hf.isCompact_preimage hs.2
#align closed_embedding.locally_compact_space ClosedEmbedding.locallyCompactSpace

protected theorem IsClosed.locallyCompactSpace [LocallyCompactSpace α] {s : Set α}
    (hs : IsClosed s) : LocallyCompactSpace s :=
  (closedEmbedding_subtype_val hs).locallyCompactSpace
#align is_closed.locally_compact_space IsClosed.locallyCompactSpace

protected theorem OpenEmbedding.locallyCompactSpace [LocallyCompactSpace β] {f : α → β}
    (hf : OpenEmbedding f) : LocallyCompactSpace α := by
  have : ∀ x : α, (𝓝 x).HasBasis
      (fun s => (s ∈ 𝓝 (f x) ∧ IsCompact s) ∧ s ⊆ range f) fun s => f ⁻¹' s := by
    intro x
    rw [hf.toInducing.nhds_eq_comap]
    exact
      ((compact_basis_nhds _).restrict_subset <| hf.open_range.mem_nhds <| mem_range_self _).comap _
  refine' locallyCompactSpace_of_hasBasis this fun x s hs => _
  rw [← hf.toInducing.isCompact_iff, image_preimage_eq_of_subset hs.2]
  exact hs.1.2
#align open_embedding.locally_compact_space OpenEmbedding.locallyCompactSpace

protected theorem IsOpen.locallyCompactSpace [LocallyCompactSpace α] {s : Set α} (hs : IsOpen s) :
    LocallyCompactSpace s :=
  hs.openEmbedding_subtype_val.locallyCompactSpace
#align is_open.locally_compact_space IsOpen.locallyCompactSpace

nonrec theorem Ultrafilter.le_nhds_lim [CompactSpace α] (F : Ultrafilter α) : ↑F ≤ 𝓝 F.lim := by
  rcases isCompact_univ.ultrafilter_le_nhds F (by simp) with ⟨x, -, h⟩
  exact le_nhds_lim ⟨x, h⟩
set_option linter.uppercaseLean3 false in
#align ultrafilter.le_nhds_Lim Ultrafilter.le_nhds_lim
