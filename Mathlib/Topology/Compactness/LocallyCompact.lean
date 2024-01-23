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

variable {X : Type*} {Y : Type*} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}


/-- We say that a topological space is a *weakly locally compact space*,
if each point of this space admits a compact neighborhood. -/
class WeaklyLocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Every point of a weakly locally compact space admits a compact neighborhood. -/
  exists_compact_mem_nhds (x : X) : ∃ s, IsCompact s ∧ s ∈ 𝓝 x

export WeaklyLocallyCompactSpace (exists_compact_mem_nhds)
#align exists_compact_mem_nhds WeaklyLocallyCompactSpace.exists_compact_mem_nhds

instance [WeaklyLocallyCompactSpace X] [WeaklyLocallyCompactSpace Y] :
    WeaklyLocallyCompactSpace (X × Y) where
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

instance (priority := 100) [CompactSpace X] : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds _ := ⟨univ, isCompact_univ, univ_mem⟩

/-- In a weakly locally compact space,
every compact set is contained in the interior of a compact set. -/
theorem exists_compact_superset [WeaklyLocallyCompactSpace X] {K : Set X} (hK : IsCompact K) :
    ∃ K', IsCompact K' ∧ K ⊆ interior K' := by
  choose s hc hmem using fun x : X ↦ exists_compact_mem_nhds x
  rcases hK.elim_nhds_subcover _ fun x _ ↦ interior_mem_nhds.2 (hmem x) with ⟨I, -, hIK⟩
  refine ⟨⋃ x ∈ I, s x, I.isCompact_biUnion fun _ _ ↦ hc _, hIK.trans ?_⟩
  exact iUnion₂_subset fun x hx ↦ interior_mono <| subset_iUnion₂ (s := fun x _ ↦ s x) x hx
#align exists_compact_superset exists_compact_superset

/-- In a weakly locally compact space,
the filters `𝓝 x` and `cocompact X` are disjoint for all `X`. -/
theorem disjoint_nhds_cocompact [WeaklyLocallyCompactSpace X] (x : X) :
    Disjoint (𝓝 x) (cocompact X) :=
  let ⟨_, hc, hx⟩ := exists_compact_mem_nhds x
  disjoint_of_disjoint_of_mem disjoint_compl_right hx hc.compl_mem_cocompact

/-- There are various definitions of "locally compact space" in the literature,
which agree for Hausdorff spaces but not in general.
This one is the precise condition on X needed
for the evaluation map `C(X, Y) × X → Y` to be continuous for all `Y`
when `C(X, Y)` is given the compact-open topology.

See also `WeaklyLocallyCompactSpace`, a typeclass that only assumes
that each point has a compact neighborhood. -/
class LocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a locally compact space,
    every neighbourhood of every point contains a compact neighbourhood of that same point. -/
  local_compact_nhds : ∀ (x : X), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s
#align locally_compact_space LocallyCompactSpace

theorem compact_basis_nhds [LocallyCompactSpace X] (x : X) :
    (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x ∧ IsCompact s) fun s => s :=
  hasBasis_self.2 <| by simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x
#align compact_basis_nhds compact_basis_nhds

theorem local_compact_nhds [LocallyCompactSpace X] {x : X} {n : Set X} (h : n ∈ 𝓝 x) :
    ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s :=
  LocallyCompactSpace.local_compact_nhds _ _ h
#align local_compact_nhds local_compact_nhds

theorem LocallyCompactSpace.of_hasBasis {ι : X → Type*} {p : ∀ x, ι x → Prop}
    {s : ∀ x, ι x → Set X} (h : ∀ x, (𝓝 x).HasBasis (p x) (s x))
    (hc : ∀ x i, p x i → IsCompact (s x i)) : LocallyCompactSpace X :=
  ⟨fun x _t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩
#align locally_compact_space_of_has_basis LocallyCompactSpace.of_hasBasis

@[deprecated] -- since 29 Dec 2023
alias locallyCompactSpace_of_hasBasis := LocallyCompactSpace.of_hasBasis

instance Prod.locallyCompactSpace (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    LocallyCompactSpace (X × Y) :=
  have := fun x : X × Y => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
 .of_hasBasis this fun _ _ ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂
#align prod.locally_compact_space Prod.locallyCompactSpace

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
    refine' ⟨(Set.univ : Set ι).pi n'', _, subset_trans (fun _ h => _) hsub, isCompact_univ_pi hc⟩
    · exact (set_pi_mem_nhds_iff (@Set.finite_univ ι _) _).mpr fun i _ => hn'' i
    · exact fun i _ => hsub' i (h i trivial)⟩
#align pi.locally_compact_space_of_finite Pi.locallyCompactSpace_of_finite

/-- For spaces that are not Hausdorff. -/
instance Pi.locallyCompactSpace [∀ i, CompactSpace (X i)] : LocallyCompactSpace (∀ i, X i) :=
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

instance Function.locallyCompactSpace_of_finite [Finite ι] [LocallyCompactSpace Y] :
    LocallyCompactSpace (ι → Y) :=
  Pi.locallyCompactSpace_of_finite
#align function.locally_compact_space_of_finite Function.locallyCompactSpace_of_finite

instance Function.locallyCompactSpace [LocallyCompactSpace Y] [CompactSpace Y] :
    LocallyCompactSpace (ι → Y) :=
  Pi.locallyCompactSpace
#align function.locally_compact_space Function.locallyCompactSpace

end Pi

/-- We say that `X` and `Y` are a locally compact pair of topological spaces,
if for any continuous map `f : X → Y`, a point `x : X`, and a neighbourhood `s ∈ 𝓝 (f x)`,
there exists a compact neighbourhood `K ∈ 𝓝 x` such that `f` maps `K` to `s`.

This is a technical assumption that appears in several theorems,
most notably in `ContinuousMap.continuous_comp'` and `ContinuousMap.continuous_eval`.
It is satisfied in two cases:

- if `X` is a locally compact topological space, for obvious reasons;
- if `X` is a weakly locally compact topological space and `Y` is a Hausdorff space;
  this fact is a simple generalization of the theorem
  saying that a weakly locally compact Hausdorff topological space is locally compact.
-/
class LocallyCompactPair (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  /-- If `f : X → Y` is a continuous map in a locally compact pair of topological spaces
  and `s : Set Y` is a neighbourhood of `f x`, `x : X`,
  then there exists a compact neighbourhood `K` of `x` such that `f` maps `K` to `s`. -/
  exists_mem_nhds_isCompact_mapsTo : ∀ {f : X → Y} {x : X} {s : Set Y},
    Continuous f → s ∈ 𝓝 (f x) → ∃ K ∈ 𝓝 x, IsCompact K ∧ MapsTo f K s

export LocallyCompactPair (exists_mem_nhds_isCompact_mapsTo)

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
#align exists_compact_subset exists_compact_subset

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
  exact ⟨_, hKs, s.isCompact_biUnion fun x hx ↦ hVc x (hsK x hx), mapsTo_iUnion₂ fun x hx ↦
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
#align exists_compact_between exists_compact_between

protected theorem ClosedEmbedding.locallyCompactSpace [LocallyCompactSpace Y] {f : X → Y}
    (hf : ClosedEmbedding f) : LocallyCompactSpace X :=
  haveI : ∀ x : X, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (f x) ∧ IsCompact s) (f ⁻¹' ·) := fun x ↦ by
    rw [hf.toInducing.nhds_eq_comap]
    exact (compact_basis_nhds _).comap _
  .of_hasBasis this fun x s hs => hf.isCompact_preimage hs.2
#align closed_embedding.locally_compact_space ClosedEmbedding.locallyCompactSpace

protected theorem IsClosed.locallyCompactSpace [LocallyCompactSpace X] {s : Set X}
    (hs : IsClosed s) : LocallyCompactSpace s :=
  (closedEmbedding_subtype_val hs).locallyCompactSpace
#align is_closed.locally_compact_space IsClosed.locallyCompactSpace

protected theorem OpenEmbedding.locallyCompactSpace [LocallyCompactSpace Y] {f : X → Y}
    (hf : OpenEmbedding f) : LocallyCompactSpace X := by
  have : ∀ x : X,
      (𝓝 x).HasBasis (fun s ↦ (s ∈ 𝓝 (f x) ∧ IsCompact s) ∧ s ⊆ range f) (f ⁻¹' ·) := fun x ↦ by
    rw [hf.nhds_eq_comap]
    exact ((compact_basis_nhds _).restrict_subset <| hf.open_range.mem_nhds <|
      mem_range_self _).comap _
  refine .of_hasBasis this fun x s hs => ?_
  rw [hf.toInducing.isCompact_iff, image_preimage_eq_of_subset hs.2]
  exact hs.1.2
#align open_embedding.locally_compact_space OpenEmbedding.locallyCompactSpace

protected theorem IsOpen.locallyCompactSpace [LocallyCompactSpace X] {s : Set X} (hs : IsOpen s) :
    LocallyCompactSpace s :=
  hs.openEmbedding_subtype_val.locallyCompactSpace
#align is_open.locally_compact_space IsOpen.locallyCompactSpace
