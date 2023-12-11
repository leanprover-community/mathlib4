/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Topology.Homeomorph
import Mathlib.Topology.StoneCech
import Mathlib.Topology.Filter
import Mathlib.Order.Filter.Cofinite

/-!
# Proper maps between topological spaces

This file develops the basic theory of proper maps between topological spaces. A map `f : X → Y`
between two topological spaces is said to be **proper** if it is continuous and satisfies
the following equivalent conditions:
1. `f` is closed and has compact fibers.
2. `f` is **universally closed**, in the sense that for any topological space `Z`, the map
  `Prod.map f id : X × Z → Y × Z` is closed.
3. For any `ℱ : Filter X`, all cluster points of `map f ℱ` are images by `f` of some cluster point
  of `ℱ`.

We take 3 as the definition in `IsProperMap`, and we show the equivalence with 1, 2, and some
other variations. We also show the usual characterization of proper maps to a locally compact
Hausdorff space as continuous maps such that preimages of compact sets are compact.

## Main statements

* `isProperMap_iff_ultrafilter`: characterization of proper maps in terms of limits of ultrafilters
  instead of cluster points of filters.
* `IsProperMap.pi_map`: any product of proper maps is proper.
* `isProperMap_iff_isClosedMap_and_compact_fibers`: a map is proper if and only if it is
  continuous, closed, and has compact fibers
* `isProperMap_iff_isCompact_preimage`: a map to a locally compact Hausdorff space is proper if
  and only if it is continuous and preimages of compact sets are compact.
* `isProperMap_iff_universally_closed`: a map is proper if and only if it is continuous and
  universally closed, in the sense of condition 2. above.

## Implementation notes

In algebraic geometry, it is common to also ask that proper maps are *separated*, in the sense of
[Stacks: definition OCY1](https://stacks.math.columbia.edu/tag/0CY1). We don't follow this
convention because it is unclear whether it would give the right notion in all cases, and in
particular for the theory of proper group actions. That means that our terminology does **NOT**
align with that of [Stacks: Characterizing proper maps](https://stacks.math.columbia.edu/tag/005M),
instead our definition of `IsProperMap` coincides with what they call "Bourbaki-proper".

Regarding the proofs, we don't really follow Bourbaki and go for more filter-heavy proofs,
as usual. In particular, their arguments rely heavily on restriction of closed maps (see
`IsClosedMap.restrictPreimage`), which makes them somehow annoying to formalize in type theory.
In contrast, the filter-based proofs work really well thanks to the existing API.

In fact, the filter proofs work so well that I thought this would be a great pedagogical resource
about how we use filters. For that reason, **all interesting proofs in this file are commented**,
so don't hesitate to have a look!

## TODO

* prove the equivalence with condition 3 of
  [Stacks: Theorem 005R](https://stacks.math.columbia.edu/tag/005R). Note that they mean something
  different by "universally closed".

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [Stacks: Characterizing proper maps](https://stacks.math.columbia.edu/tag/005M)
-/

set_option autoImplicit true

open Filter Topology Function Set
open Prod (fst snd)



variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  {f : X → Y}

/-- A map `f : X → Y` between two topological spaces is said to be **proper** if it is continuous
and, for all `ℱ : Filter X`, any cluster point of `map f ℱ` is the image by `f` of a cluster point
of `ℱ`. -/
@[mk_iff isProperMap_iff_clusterPt]
structure IsProperMap (f : X → Y) extends Continuous f : Prop where
  /-- By definition, if `f` is a proper map and `ℱ` is any filter on `X`, then any cluster point of
  `map f ℱ` is the image by `f` of some cluster point of `ℱ`. -/
  clusterPt_of_mapClusterPt :
    ∀ ⦃ℱ : Filter X⦄, ∀ ⦃y : Y⦄, MapClusterPt y ℱ f → ∃ x, f x = y ∧ ClusterPt x ℱ

/-- Definition of proper maps. See also `isClosedMap_iff_clusterPt` for a related criterion
for closed maps. -/
add_decl_doc isProperMap_iff_clusterPt

/-- By definition, a proper map is continuous. -/
lemma IsProperMap.continuous (h : IsProperMap f) : Continuous f := h.toContinuous

/-- An homeomorphism is proper. -/
@[simp] lemma Homeomorph.isProperMap (e : X ≃ₜ Y) : IsProperMap e := by
  rw [isProperMap_iff_clusterPt]
  refine ⟨e.continuous, fun ℱ y ↦ ?_⟩
  simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, e.comap_nhds_eq,
    ← e.coe_toEquiv, ← e.eq_symm_apply, exists_eq_left]
  exact id

/-- The identity is proper. -/
@[simp] lemma isProperMap_id : IsProperMap (id : X → X) := (Homeomorph.refl X).isProperMap

/-- A proper map is closed. -/
lemma IsProperMap.isClosedMap (h : IsProperMap f) : IsClosedMap f := by
  rw [isClosedMap_iff_clusterPt]
  exact fun s y ↦ h.clusterPt_of_mapClusterPt (ℱ := 𝓟 s) (y := y)

/-- Characterization of proper maps by ultrafilters. -/
lemma isProperMap_iff_ultrafilter : IsProperMap f ↔ Continuous f ∧
    ∀ ⦃𝒰 : Ultrafilter X⦄, ∀ ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) → ∃ x, f x = y ∧ 𝒰 ≤ 𝓝 x := by
  -- This is morally trivial since ultrafilters give all the information about cluster points.
  rw [isProperMap_iff_clusterPt]
  refine and_congr_right (fun _ ↦ ?_)
  constructor <;> intro H
  · intro 𝒰 y (hY : (Ultrafilter.map f 𝒰 : Filter Y) ≤ _)
    simp_rw [← Ultrafilter.clusterPt_iff] at hY ⊢
    exact H hY
  · simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, ← exists_ultrafilter_iff,
      forall_exists_index]
    intro ℱ y 𝒰 hy
    rcases H (tendsto_iff_comap.mpr <| hy.trans inf_le_left) with ⟨x, hxy, hx⟩
    exact ⟨x, hxy, 𝒰, le_inf hx (hy.trans inf_le_right)⟩

lemma isProperMap_iff_ultrafilter_of_t2 [T2Space Y] : IsProperMap f ↔ Continuous f ∧
    ∀ ⦃𝒰 : Ultrafilter X⦄, ∀ ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) → ∃ x, 𝒰.1 ≤ 𝓝 x :=
  isProperMap_iff_ultrafilter.trans <| and_congr_right fun hc ↦ forall₃_congr fun _𝒰 _y hy ↦
    exists_congr fun x ↦ and_iff_right_of_imp fun h ↦
      tendsto_nhds_unique ((hc.tendsto x).mono_left h) hy

/-- If `f` is proper and converges to `y` along some ultrafilter `𝒰`, then `𝒰` converges to some
`x` such that `f x = y`. -/
lemma IsProperMap.ultrafilter_le_nhds_of_tendsto (h : IsProperMap f) ⦃𝒰 : Ultrafilter X⦄ ⦃y : Y⦄
    (hy : Tendsto f 𝒰 (𝓝 y)) : ∃ x, f x = y ∧ 𝒰 ≤ 𝓝 x :=
  (isProperMap_iff_ultrafilter.mp h).2 hy

/-- A binary product of proper maps is proper. -/
lemma IsProperMap.prod_map {g : Z → W} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (Prod.map f g) := by
  simp_rw [isProperMap_iff_ultrafilter] at hf hg ⊢
  constructor
  -- Continuity is clear.
  · exact hf.1.prod_map hg.1
  -- Let `𝒰 : Ultrafilter (X × Z)`, and assume that `f × g` tends to some `(y, w) : Y × W`
  -- along `𝒰`.
  · intro 𝒰 ⟨y, w⟩ hyw
  -- That means that `f` tends to `y` along `map fst 𝒰` and `g` tends to `w` along `map snd 𝒰`.
    simp_rw [nhds_prod_eq, tendsto_prod_iff'] at hyw
  -- Thus, by properness of `f` and `g`, we get some `x : X` and `z : Z` such that `f x = y`,
  -- `g z = w`, `map fst 𝒰` tends to  `x`, and `map snd 𝒰` tends to `y`.
    rcases hf.2 (show Tendsto f (Ultrafilter.map fst 𝒰) (𝓝 y) by simpa using hyw.1) with
      ⟨x, hxy, hx⟩
    rcases hg.2 (show Tendsto g (Ultrafilter.map snd 𝒰) (𝓝 w) by simpa using hyw.2) with
      ⟨z, hzw, hz⟩
  -- By the properties of the product topology, that means that `𝒰` tends to `(x, z)`,
  -- which completes the proof since `(f × g)(x, z) = (y, w)`.
    refine ⟨⟨x, z⟩, Prod.ext hxy hzw, ?_⟩
    rw [nhds_prod_eq, le_prod]
    exact ⟨hx, hz⟩

/-- Any product of proper maps is proper. -/
lemma IsProperMap.pi_map {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : (i : ι) → X i → Y i} (h : ∀ i, IsProperMap (f i)) :
    IsProperMap (fun (x : ∀ i, X i) i ↦ f i (x i)) := by
  simp_rw [isProperMap_iff_ultrafilter] at h ⊢
  constructor
  -- Continuity is clear.
  · exact continuous_pi fun i ↦ (h i).1.comp (continuous_apply i)
  -- Let `𝒰 : Ultrafilter (Π i, X i)`, and assume that `Π i, f i` tends to some `y : Π i, Y i`
  -- along `𝒰`.
  · intro 𝒰 y hy
  -- That means that each `f i` tends to `y i` along `map (eval i) 𝒰`.
    have : ∀ i, Tendsto (f i) (Ultrafilter.map (eval i) 𝒰) (𝓝 (y i)) := by
      simpa [tendsto_pi_nhds] using hy
  -- Thus, by properness of all the `f i`s, we can choose some `x : Π i, X i` such that, for all
  -- `i`, `f i (x i) = y i` and `map (eval i) 𝒰` tends to  `x i`.
    choose x hxy hx using fun i ↦ (h i).2 (this i)
  -- By the properties of the product topology, that means that `𝒰` tends to `x`,
  -- which completes the proof since `(Π i, f i) x = y`.
    refine ⟨x, funext hxy, ?_⟩
    rwa [nhds_pi, le_pi]

/-- The preimage of a compact set by a proper map is again compact. See also
`isProperMap_iff_isCompact_preimage` which proves that this property completely characterizes
proper map when the codomain is locally compact and Hausdorff. -/
lemma IsProperMap.isCompact_preimage (h : IsProperMap f) {K : Set Y} (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  -- Let `𝒰 ≤ 𝓟 (f ⁻¹' K)` an ultrafilter.
  intro 𝒰 h𝒰
  -- In other words, we have `map f 𝒰 ≤ 𝓟 K`
  rw [← comap_principal, ← map_le_iff_le_comap, ← Ultrafilter.coe_map] at h𝒰
  -- Thus, by compactness of `K`, the ultrafilter `map f 𝒰` tends to some `y ∈ K`.
  rcases hK.ultrafilter_le_nhds _ h𝒰 with ⟨y, hyK, hy⟩
  -- Then, by properness of `f`, that means that `𝒰` tends to some `x ∈ f ⁻¹' {y} ⊆ f ⁻¹' K`,
  -- which completes the proof.
  rcases h.ultrafilter_le_nhds_of_tendsto hy with ⟨x, rfl, hx⟩
  exact ⟨x, hyK, hx⟩

/-- A map is proper if and only if it is closed and its fibers are compact. -/
theorem isProperMap_iff_isClosedMap_and_compact_fibers :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ ∀ y, IsCompact (f ⁻¹' {y}) := by
  constructor <;> intro H
  -- Note: In Bourbaki, the direct implication is proved by going through universally closed maps.
  -- We could do the same (using a `TFAE` cycle) but proving it directly from
  -- `IsProperMap.isCompact_preimage` is nice enough already so we don't bother with that.
  · exact ⟨H.continuous, H.isClosedMap, fun y ↦ H.isCompact_preimage isCompact_singleton⟩
  · rw [isProperMap_iff_clusterPt]
  -- Let `ℱ : Filter X` and `y` some cluster point of `map f ℱ`.
    refine ⟨H.1, fun ℱ y hy ↦ ?_⟩
  -- That means that the singleton `pure y` meets the "closure" of `map f ℱ`, by which we mean
  -- `Filter.lift' (map f ℱ) closure`. But `f` is closed, so
  -- `closure (map f ℱ) = map f (closure ℱ)` (see `IsClosedMap.lift'_closure_map_eq`).
  -- Thus `map f (closure ℱ ⊓ 𝓟 (f ⁻¹' {y})) = map f (closure ℱ) ⊓ 𝓟 {y} ≠ ⊥`, hence
  -- `closure ℱ ⊓ 𝓟 (f ⁻¹' {y}) ≠ ⊥`.
    rw [H.2.1.mapClusterPt_iff_lift'_closure H.1] at hy
  -- Now, applying the compactness of `f ⁻¹' {y}` to the nontrivial filter
  -- `closure ℱ ⊓ 𝓟 (f ⁻¹' {y})`, we obtain that it has a cluster point `x ∈ f ⁻¹' {y}`.
    rcases H.2.2 y (f := Filter.lift' ℱ closure ⊓ 𝓟 (f ⁻¹' {y})) inf_le_right with ⟨x, hxy, hx⟩
    refine ⟨x, hxy, ?_⟩
  -- In particular `x` is a cluster point of `closure ℱ`. Since cluster points of `closure ℱ`
  -- are exactly cluster points of `ℱ` (see `clusterPt_lift'_closure_iff`), this completes
  -- the proof.
    rw [← clusterPt_lift'_closure_iff]
    exact hx.mono inf_le_left

/-- Version of `isProperMap_iff_isClosedMap_and_compact_fibers` in terms of `cofinite` and
`cocompact`. Only works when the codomain is `T1`. -/
lemma isProperMap_iff_isClosedMap_and_tendsto_cofinite [T1Space Y] :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ Tendsto f (cocompact X) cofinite := by
  simp_rw [isProperMap_iff_isClosedMap_and_compact_fibers, Tendsto,
    le_cofinite_iff_compl_singleton_mem, mem_map, preimage_compl]
  refine and_congr_right fun f_cont ↦ and_congr_right fun _ ↦
    ⟨fun H y ↦ (H y).compl_mem_cocompact, fun H y ↦ ?_⟩
  rcases mem_cocompact.mp (H y) with ⟨K, hK, hKy⟩
  exact hK.of_isClosed_subset (isClosed_singleton.preimage f_cont)
    (compl_le_compl_iff_le.mp hKy)

/-- A continuous map from a compact space to a T₂ space is a proper map. -/
theorem Continuous.isProperMap [CompactSpace X] [T2Space Y] (hf : Continuous f) : IsProperMap f :=
  isProperMap_iff_isClosedMap_and_tendsto_cofinite.2 ⟨hf, hf.isClosedMap, by simp⟩

/-- If `Y` is locally compact and Hausdorff, then proper maps `X → Y` are exactly continuous maps
such that the preimage of any compact set is compact. -/
theorem isProperMap_iff_isCompact_preimage [T2Space Y] [WeaklyLocallyCompactSpace Y] :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃K⦄, IsCompact K → IsCompact (f ⁻¹' K) := by
  constructor <;> intro H
  -- The direct implication follows from the previous results
  · exact ⟨H.continuous, fun K hK ↦ H.isCompact_preimage hK⟩
  · rw [isProperMap_iff_ultrafilter_of_t2]
    -- Let `𝒰 : Ultrafilter X`, and assume that `f` tends to some `y` along `𝒰`.
    refine ⟨H.1, fun 𝒰 y hy ↦ ?_⟩
    -- Pick `K` some compact neighborhood of `y`, which exists by local compactness.
    rcases exists_compact_mem_nhds y with ⟨K, hK, hKy⟩
    -- Then `map f 𝒰 ≤ 𝓝 y ≤ 𝓟 K`, hence `𝒰 ≤ 𝓟 (f ⁻¹' K)`
    have : 𝒰 ≤ 𝓟 (f ⁻¹' K) := by
      simpa only [← comap_principal, ← tendsto_iff_comap] using
        hy.mono_right (le_principal_iff.mpr hKy)
    -- By compactness of `f ⁻¹' K`, `𝒰` converges to some `x ∈ f ⁻¹' K`.
    rcases (H.2 hK).ultrafilter_le_nhds _ this with ⟨x, -, hx⟩
    exact ⟨x, hx⟩

/-- Version of `isProperMap_iff_isCompact_preimage` in terms of `cocompact`. -/
lemma isProperMap_iff_tendsto_cocompact [T2Space Y] [WeaklyLocallyCompactSpace Y] :
    IsProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y) := by
  simp_rw [isProperMap_iff_isCompact_preimage, hasBasis_cocompact.tendsto_right_iff,
    ← mem_preimage, eventually_mem_set, preimage_compl]
  refine and_congr_right fun f_cont ↦
    ⟨fun H K hK ↦ (H hK).compl_mem_cocompact, fun H K hK ↦ ?_⟩
  rcases mem_cocompact.mp (H K hK) with ⟨K', hK', hK'y⟩
  exact hK'.of_isClosed_subset (hK.isClosed.preimage f_cont)
    (compl_le_compl_iff_le.mp hK'y)

/-- A proper map `f : X → Y` is **universally closed**: for any topological space `Z`, the map
`Prod.map f id : X × Z → Y × Z` is closed. We will prove in `isProperMap_iff_universally_closed`
that proper maps are exactly continuous maps which have this property, but this result should be
easier to use because it allows `Z` to live in any universe. -/
theorem IsProperMap.universally_closed (Z) [TopologicalSpace Z] (h : IsProperMap f) :
    IsClosedMap (Prod.map f id : X × Z → Y × Z) :=
  -- `f × id` is proper as a product of proper maps, hence closed.
  (h.prod_map isProperMap_id).isClosedMap

/-- A map `f : X → Y` is proper if and only if it is continuous and the map
`(Prod.map f id : X × Filter X → Y × Filter X)` is closed. This is stronger than
`isProperMap_iff_universally_closed` since it shows that there's only one space to check to get
properness, but in most cases it doesn't matter. -/
theorem isProperMap_iff_isClosedMap_filter {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap
      (Prod.map f id : X × Filter X → Y × Filter X) := by
  constructor <;> intro H
  -- The direct implication is clear.
  · exact ⟨H.continuous, H.universally_closed _⟩
  · rw [isProperMap_iff_ultrafilter]
  -- Let `𝒰 : Ultrafilter X`, and assume that `f` tends to some `y` along `𝒰`.
    refine ⟨H.1, fun 𝒰 y hy ↦ ?_⟩
  -- In `X × Filter X`, consider the closed set `F := closure {(x, ℱ) | ℱ = pure x}`
    let F : Set (X × Filter X) := closure {xℱ | xℱ.2 = pure xℱ.1}
  -- Since `f × id` is closed, the set `(f × id) '' F` is also closed.
    have := H.2 F isClosed_closure
  -- Let us show that `(y, 𝒰) ∈ (f × id) '' F`.
    have : (y, ↑𝒰) ∈ Prod.map f id '' F :=
  -- Note that, by the properties of the topology on `Filter X`, the function `pure : X → Filter X`
  -- tends to the point `𝒰` of `Filter X` along the filter `𝒰` on `X`. Since `f` tends to `y` along
  -- `𝒰`, we get that the function `(f, pure) : X → (Y, Filter X)` tends to `(y, 𝒰)` along
  -- `𝒰`. Furthermore, each `(f, pure)(x) = (f × id)(x, pure x)` is clearly an element of
  -- the closed set `(f × id) '' F`, thus the limit `(y, 𝒰)` also belongs to that set.
      this.mem_of_tendsto (hy.prod_mk_nhds (Filter.tendsto_pure_self (𝒰 : Filter X)))
        (eventually_of_forall fun x ↦ ⟨⟨x, pure x⟩, subset_closure rfl, rfl⟩)
  -- The above shows that `(y, 𝒰) = (f x, 𝒰)`, for some `x : X` such that `(x, 𝒰) ∈ F`.
    rcases this with ⟨⟨x, _⟩, hx, ⟨_, _⟩⟩
  -- We already know that `f x = y`, so to finish the proof we just have to check that `𝒰` tends
  -- to `x`. So, for `U ∈ 𝓝 x` arbitrary, let's show that `U ∈ 𝒰`. Since `𝒰` is a ultrafilter,
  -- it is enough to show that `Uᶜ` is not in `𝒰`.
    refine ⟨x, rfl, fun U hU ↦ Ultrafilter.compl_not_mem_iff.mp fun hUc ↦ ?_⟩
    rw [mem_closure_iff_nhds] at hx
  -- Indeed, if that was the case, the set `V := {𝒢 : Filter X | Uᶜ ∈ 𝒢}` would be a neighborhood
  -- of `𝒰` in `Filter X`, hence `U ×ˢ V` would be a neighborhood of `(x, 𝒰) : X × Filter X`.
  -- But recall that `(x, 𝒰) ∈ F = closure {(x, ℱ) | ℱ = pure x}`, so the neighborhood `U ×ˢ V`
  -- must contain some element of the form `(z, pure z)`. In other words, we have `z ∈ U` and
  -- `Uᶜ ∈ pure z`, which means `z ∈ Uᶜ` by the definition of pure.
  -- This is a contradiction, which completes the proof.
    rcases hx (U ×ˢ {𝒢 | Uᶜ ∈ 𝒢}) (prod_mem_nhds hU (isOpen_setOf_mem.mem_nhds hUc)) with
      ⟨⟨z, 𝒢⟩, ⟨⟨hz : z ∈ U, hz' : Uᶜ ∈ 𝒢⟩, rfl : 𝒢 = pure z⟩⟩
    exact hz' hz

/-- A map `f : X → Y` is proper if and only if it is continuous and the map
`(Prod.map f id : X × Ultrafilter X → Y × Ultrafilter X)` is closed. This is stronger than
`isProperMap_iff_universally_closed` since it shows that there's only one space to check to get
properness, but in most cases it doesn't matter. -/
theorem isProperMap_iff_isClosedMap_ultrafilter {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap
      (Prod.map f id : X × Ultrafilter X → Y × Ultrafilter X) := by
  -- The proof is basically the same as above.
  constructor <;> intro H
  · exact ⟨H.continuous, H.universally_closed _⟩
  · rw [isProperMap_iff_ultrafilter]
    refine ⟨H.1, fun 𝒰 y hy ↦ ?_⟩
    let F : Set (X × Ultrafilter X) := closure {xℱ | xℱ.2 = pure xℱ.1}
    have := H.2 F isClosed_closure
    have : (y, 𝒰) ∈ Prod.map f id '' F :=
      this.mem_of_tendsto (hy.prod_mk_nhds (Ultrafilter.tendsto_pure_self 𝒰))
        (eventually_of_forall fun x ↦ ⟨⟨x, pure x⟩, subset_closure rfl, rfl⟩)
    rcases this with ⟨⟨x, _⟩, hx, ⟨_, _⟩⟩
    refine ⟨x, rfl, fun U hU ↦ Ultrafilter.compl_not_mem_iff.mp fun hUc ↦ ?_⟩
    rw [mem_closure_iff_nhds] at hx
    rcases hx (U ×ˢ {𝒢 | Uᶜ ∈ 𝒢}) (prod_mem_nhds hU ((ultrafilter_isOpen_basic _).mem_nhds hUc))
      with ⟨⟨y, 𝒢⟩, ⟨⟨hy : y ∈ U, hy' : Uᶜ ∈ 𝒢⟩, rfl : 𝒢 = pure y⟩⟩
    exact hy' hy

/-- A map `f : X → Y` is proper if and only if it is continuous and **universally closed**, in the
sense that for any topological space `Z`, the map `Prod.map f id : X × Z → Y × Z` is closed. Note
that `Z` lives in the same universe as `X` here, but `IsProperMap.universally_closed` does not
have this restriction.

This is taken as the definition of properness in
[N. Bourbaki, *General Topology*][bourbaki1966]. -/
theorem isProperMap_iff_universally_closed {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ ∀ (Z : Type u) [TopologicalSpace Z],
      IsClosedMap (Prod.map f id : X × Z → Y × Z) := by
  constructor <;> intro H
  · exact ⟨H.continuous, fun Z ↦ H.universally_closed _⟩
  · rw [isProperMap_iff_isClosedMap_ultrafilter]
    exact ⟨H.1, H.2 _⟩
