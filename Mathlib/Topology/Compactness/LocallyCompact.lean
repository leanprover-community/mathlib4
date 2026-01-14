/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Compactness.Compact
/-!
# Locally compact spaces

This file contains basic results about locally compact spaces.
-/

open Set Filter Topology TopologicalSpace

variable {X : Type*} {Y : Type*} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

instance [WeaklyLocallyCompactSpace X] [WeaklyLocallyCompactSpace Y] :
    WeaklyLocallyCompactSpace (X × Y) where
  exists_compact_mem_nhds x :=
    let ⟨s₁, hc₁, h₁⟩ := exists_compact_mem_nhds x.1
    let ⟨s₂, hc₂, h₂⟩ := exists_compact_mem_nhds x.2
    ⟨s₁ ×ˢ s₂, hc₁.prod hc₂, prod_mem_nhds h₁ h₂⟩

instance {ι : Type*} [Finite ι] {X : ι → Type*} [(i : ι) → TopologicalSpace (X i)]
    [(i : ι) → WeaklyLocallyCompactSpace (X i)] :
    WeaklyLocallyCompactSpace ((i : ι) → X i) where
  exists_compact_mem_nhds f := by
    choose s hsc hs using fun i ↦ exists_compact_mem_nhds (f i)
    exact ⟨pi univ s, isCompact_univ_pi hsc, set_pi_mem_nhds univ.toFinite fun i _ ↦ hs i⟩

instance (priority := 100) [CompactSpace X] : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds _ := ⟨univ, isCompact_univ, univ_mem⟩

protected theorem Topology.IsClosedEmbedding.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace Y]
    {f : X → Y} (hf : IsClosedEmbedding f) : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x :=
    let ⟨K, hK, hKx⟩ := exists_compact_mem_nhds (f x)
    ⟨f ⁻¹' K, hf.isCompact_preimage hK, hf.continuous.continuousAt hKx⟩

protected theorem IsClosed.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) : WeaklyLocallyCompactSpace s :=
  hs.isClosedEmbedding_subtypeVal.weaklyLocallyCompactSpace

theorem IsOpenQuotientMap.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace X]
    {f : X → Y} (hf : IsOpenQuotientMap f) : WeaklyLocallyCompactSpace Y where
  exists_compact_mem_nhds := by
    refine hf.surjective.forall.2 fun x ↦ ?_
    rcases exists_compact_mem_nhds x with ⟨K, hKc, hKx⟩
    exact ⟨f '' K, hKc.image hf.continuous, hf.isOpenMap.image_mem_nhds hKx⟩

/-- In a weakly locally compact space,
every compact set is contained in the interior of a compact set. -/
theorem exists_compact_superset [WeaklyLocallyCompactSpace X] {K : Set X} (hK : IsCompact K) :
    ∃ K', IsCompact K' ∧ K ⊆ interior K' := by
  choose s hc hmem using fun x : X ↦ exists_compact_mem_nhds x
  rcases hK.elim_nhds_subcover _ fun x _ ↦ interior_mem_nhds.2 (hmem x) with ⟨I, -, hIK⟩
  refine ⟨⋃ x ∈ I, s x, I.isCompact_biUnion fun _ _ ↦ hc _, hIK.trans ?_⟩
  exact iUnion₂_subset fun x hx ↦ interior_mono <| subset_iUnion₂ (s := fun x _ ↦ s x) x hx

/-- In a weakly locally compact space,
the filters `𝓝 x` and `cocompact X` are disjoint for all `X`. -/
theorem disjoint_nhds_cocompact [WeaklyLocallyCompactSpace X] (x : X) :
    Disjoint (𝓝 x) (cocompact X) :=
  let ⟨_, hc, hx⟩ := exists_compact_mem_nhds x
  disjoint_of_disjoint_of_mem disjoint_compl_right hx hc.compl_mem_cocompact

theorem compact_basis_nhds [LocallyCompactSpace X] (x : X) :
    (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x ∧ IsCompact s) fun s => s :=
  hasBasis_self.2 <| by simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x

theorem local_compact_nhds [LocallyCompactSpace X] {x : X} {n : Set X} (h : n ∈ 𝓝 x) :
    ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s :=
  LocallyCompactSpace.local_compact_nhds _ _ h

theorem LocallyCompactSpace.of_hasBasis {ι : X → Type*} {p : ∀ x, ι x → Prop}
    {s : ∀ x, ι x → Set X} (h : ∀ x, (𝓝 x).HasBasis (p x) (s x))
    (hc : ∀ x i, p x i → IsCompact (s x i)) : LocallyCompactSpace X :=
  ⟨fun x _t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩

instance Prod.locallyCompactSpace (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    LocallyCompactSpace (X × Y) :=
  have := fun x : X × Y => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
  .of_hasBasis this fun _ _ ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂

section Pi

variable {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, LocallyCompactSpace (X i)]

/-- In general it suffices that all but finitely many of the spaces are compact,
  but that's not straightforward to state and use. -/
instance Pi.locallyCompactSpace_of_finite [Finite ι] : LocallyCompactSpace (∀ i, X i) :=
  ⟨fun t n hn => by
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨s, -, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨(Set.univ : Set ι).pi n'', ?_, subset_trans (fun _ h => ?_) hsub, isCompact_univ_pi hc⟩
    · exact (set_pi_mem_nhds_iff (@Set.finite_univ ι _) _).mpr fun i _ => hn'' i
    · exact fun i _ => hsub' i (h i trivial)⟩

/-- For spaces that are not Hausdorff. -/
instance Pi.locallyCompactSpace [∀ i, CompactSpace (X i)] : LocallyCompactSpace (∀ i, X i) :=
  ⟨fun t n hn => by
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨s, hs, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨s.pi n'', ?_, subset_trans (fun _ => ?_) hsub, ?_⟩
    · exact (set_pi_mem_nhds_iff hs _).mpr fun i _ => hn'' i
    · exact forall₂_imp fun i _ hi' => hsub' i hi'
    · classical
      rw [← Set.univ_pi_ite]
      refine isCompact_univ_pi fun i => ?_
      by_cases h : i ∈ s
      · rw [if_pos h]
        exact hc i
      · rw [if_neg h]
        exact CompactSpace.isCompact_univ⟩

instance Function.locallyCompactSpace_of_finite [Finite ι] [LocallyCompactSpace Y] :
    LocallyCompactSpace (ι → Y) :=
  Pi.locallyCompactSpace_of_finite

instance Function.locallyCompactSpace [LocallyCompactSpace Y] [CompactSpace Y] :
    LocallyCompactSpace (ι → Y) :=
  Pi.locallyCompactSpace

end Pi

instance (priority := 900) [LocallyCompactSpace X] : LocallyCompactPair X Y where
  exists_mem_nhds_isCompact_mapsTo hf hs :=
    let ⟨K, hKx, hKs, hKc⟩ := local_compact_nhds (hf.continuousAt hs); ⟨K, hKx, hKc, hKs⟩

instance (priority := 100) [LocallyCompactSpace X] : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds (x : X) :=
    let ⟨K, hx, _, hKc⟩ := local_compact_nhds (x := x) univ_mem; ⟨K, hKc, hx⟩

/-- A reformulation of the definition of locally compact space: In a locally compact space,
  every open set containing `x` has a compact subset containing `x` in its interior. -/
theorem exists_compact_subset [LocallyCompactSpace X] {x : X} {U : Set X} (hU : IsOpen U)
    (hx : x ∈ U) : ∃ K : Set X, IsCompact K ∧ x ∈ interior K ∧ K ⊆ U := by
  rcases LocallyCompactSpace.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩

/-- If `f : X → Y` is a continuous map in a locally compact pair of topological spaces,
`K : set X` is a compact set, and `U` is an open neighbourhood of `f '' K`,
then there exists a compact neighbourhood `L` of `K` such that `f` maps `L` to `U`.

This is a generalization of `exists_mem_nhds_isCompact_mapsTo`. -/
lemma exists_mem_nhdsSet_isCompact_mapsTo [LocallyCompactPair X Y] {f : X → Y} {K : Set X}
    {U : Set Y} (hf : Continuous f) (hK : IsCompact K) (hU : IsOpen U) (hKU : MapsTo f K U) :
    ∃ L ∈ 𝓝ˢ K, IsCompact L ∧ MapsTo f L U := by
  choose! V hxV hVc hVU using fun x (hx : x ∈ K) ↦
    exists_mem_nhds_isCompact_mapsTo hf (hU.mem_nhds (hKU hx))
  rcases hK.elim_nhds_subcover_nhdsSet hxV with ⟨s, hsK, hKs⟩
  exact ⟨_, hKs, s.isCompact_biUnion fun x hx ↦ hVc x (hsK x hx), mapsTo_iUnion₂.2 fun x hx ↦
    hVU x (hsK x hx)⟩

/-- In a locally compact space, for every containment `K ⊆ U` of a compact set `K` in an open
  set `U`, there is a compact neighborhood `L` such that `K ⊆ L ⊆ U`: equivalently, there is a
  compact `L` such that `K ⊆ interior L` and `L ⊆ U`.
  See also `exists_compact_closed_between`, in which one guarantees additionally that `L` is closed
  if the space is regular. -/
theorem exists_compact_between [LocallyCompactSpace X] {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (h_KU : K ⊆ U) : ∃ L, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U :=
  let ⟨L, hKL, hL, hLU⟩ := exists_mem_nhdsSet_isCompact_mapsTo continuous_id hK hU h_KU
  ⟨L, hL, subset_interior_iff_mem_nhdsSet.2 hKL, hLU⟩

theorem IsOpenQuotientMap.locallyCompactSpace [LocallyCompactSpace X] {f : X → Y}
    (hf : IsOpenQuotientMap f) : LocallyCompactSpace Y where
  local_compact_nhds := by
    refine hf.surjective.forall.2 fun x U hU ↦ ?_
    rcases local_compact_nhds (hf.continuous.continuousAt hU) with ⟨K, hKx, hKU, hKc⟩
    exact ⟨f '' K, hf.isOpenMap.image_mem_nhds hKx, image_subset_iff.2 hKU, hKc.image hf.continuous⟩

/-- If `f` is a topology inducing map with a locally compact codomain and a locally closed range,
then the domain of `f` is a locally compact space. -/
theorem Topology.IsInducing.locallyCompactSpace [LocallyCompactSpace Y] {f : X → Y}
    (hf : IsInducing f) (h : IsLocallyClosed (range f)) : LocallyCompactSpace X := by
  rcases h with ⟨U, Z, hU, hZ, hUZ⟩
  have (x : X) : (𝓝 x).HasBasis (fun s ↦ (s ∈ 𝓝 (f x) ∧ IsCompact s) ∧ s ⊆ U)
      (fun s ↦ f ⁻¹' (s ∩ Z)) := by
    have H : U ∈ 𝓝 (f x) := hU.mem_nhds (hUZ.subset <| mem_range_self _).1
    rw [hf.nhds_eq_comap, ← comap_nhdsWithin_range, hUZ,
      nhdsWithin_inter_of_mem (nhdsWithin_le_nhds H)]
    exact (nhdsWithin_hasBasis ((compact_basis_nhds (f x)).restrict_subset H) _).comap _
  refine .of_hasBasis this fun x s ⟨⟨_, hs⟩, hsU⟩ ↦ ?_
  rw [hf.isCompact_preimage_iff]
  exacts [hs.inter_right hZ, hUZ ▸ by gcongr]

protected theorem Topology.IsClosedEmbedding.locallyCompactSpace [LocallyCompactSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : LocallyCompactSpace X :=
  hf.isInducing.locallyCompactSpace hf.isClosed_range.isLocallyClosed

protected theorem Topology.IsOpenEmbedding.locallyCompactSpace [LocallyCompactSpace Y] {f : X → Y}
    (hf : IsOpenEmbedding f) : LocallyCompactSpace X :=
  hf.isInducing.locallyCompactSpace hf.isOpen_range.isLocallyClosed

protected theorem IsLocallyClosed.locallyCompactSpace [LocallyCompactSpace X] {s : Set X}
    (hs : IsLocallyClosed s) : LocallyCompactSpace s :=
  IsEmbedding.subtypeVal.locallyCompactSpace <| by rwa [Subtype.range_val]

protected theorem IsClosed.locallyCompactSpace [LocallyCompactSpace X] {s : Set X}
    (hs : IsClosed s) : LocallyCompactSpace s :=
  hs.isLocallyClosed.locallyCompactSpace

protected theorem IsOpen.locallyCompactSpace [LocallyCompactSpace X] {s : Set X} (hs : IsOpen s) :
    LocallyCompactSpace s :=
  hs.isLocallyClosed.locallyCompactSpace
