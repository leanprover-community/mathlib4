/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Etienne Marion
-/
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Filter

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
other variations.

## Main statements

* `isProperMap_iff_ultrafilter`: characterization of proper maps in terms of limits of ultrafilters
  instead of cluster points of filters.
* `IsProperMap.pi_map`: any product of proper maps is proper.
* `isProperMap_iff_isClosedMap_and_compact_fibers`: a map is proper if and only if it is
  continuous, closed, and has compact fibers

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

assert_not_exists StoneCech

open Filter Topology Function Set
open Prod (fst snd)

variable {X Y Z W ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W] {f : X → Y} {g : Y → Z}

universe u v

/-- A map `f : X → Y` between two topological spaces is said to be **proper** if it is continuous
and, for all `ℱ : Filter X`, any cluster point of `map f ℱ` is the image by `f` of a cluster point
of `ℱ`. -/
@[mk_iff isProperMap_iff_clusterPt, fun_prop]
structure IsProperMap (f : X → Y) extends Continuous f : Prop where
  /-- By definition, if `f` is a proper map and `ℱ` is any filter on `X`, then any cluster point of
  `map f ℱ` is the image by `f` of some cluster point of `ℱ`. -/
  clusterPt_of_mapClusterPt :
    ∀ ⦃ℱ : Filter X⦄, ∀ ⦃y : Y⦄, MapClusterPt y ℱ f → ∃ x, f x = y ∧ ClusterPt x ℱ

/-- Definition of proper maps. See also `isClosedMap_iff_clusterPt` for a related criterion
for closed maps. -/
add_decl_doc isProperMap_iff_clusterPt

/-- By definition, a proper map is continuous. -/
@[fun_prop]
lemma IsProperMap.continuous (h : IsProperMap f) : Continuous f := h.toContinuous

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

/-- The composition of two proper maps is proper. -/
lemma IsProperMap.comp (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (g ∘ f) := by
  refine ⟨by fun_prop, fun ℱ z h ↦ ?_⟩
  rw [mapClusterPt_comp] at h
  rcases hg.clusterPt_of_mapClusterPt h with ⟨y, rfl, hy⟩
  rcases hf.clusterPt_of_mapClusterPt hy with ⟨x, rfl, hx⟩
  use x, rfl


/-- If the composition of two continuous functions `g ∘ f` is proper and `f` is surjective,
then `g` is proper. -/
lemma isProperMap_of_comp_of_surj (hf : Continuous f)
    (hg : Continuous g) (hgf : IsProperMap (g ∘ f)) (f_surj : f.Surjective) : IsProperMap g := by
  refine ⟨hg, fun ℱ z h ↦ ?_⟩
  rw [← ℱ.map_comap_of_surjective f_surj, ← mapClusterPt_comp] at h
  rcases hgf.clusterPt_of_mapClusterPt h with ⟨x, rfl, hx⟩
  rw [← ℱ.map_comap_of_surjective f_surj]
  exact ⟨f x, rfl, hx.map hf.continuousAt tendsto_map⟩

/-- If the composition of two continuous functions `g ∘ f` is proper and `g` is injective,
then `f` is proper. -/
lemma isProperMap_of_comp_of_inj {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
    (hgf : IsProperMap (g ∘ f)) (g_inj : g.Injective) : IsProperMap f := by
  refine ⟨hf, fun ℱ y h ↦ ?_⟩
  rcases hgf.clusterPt_of_mapClusterPt (h.map hg.continuousAt tendsto_map) with ⟨x, hx1, hx2⟩
  exact ⟨x, g_inj hx1, hx2⟩

/-- If the composition of two continuous functions `f : X → Y` and `g : Y → Z` is proper
and `Y` is T2, then `f` is proper. -/
lemma isProperMap_of_comp_of_t2 [T2Space Y] (hf : Continuous f) (hg : Continuous g)
    (hgf : IsProperMap (g ∘ f)) : IsProperMap f := by
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨hf, fun 𝒰 y h ↦ ?_⟩
  rw [isProperMap_iff_ultrafilter] at hgf
  rcases hgf.2 ((hg.tendsto y).comp h) with ⟨x, -, hx⟩
  exact ⟨x, hx⟩

/-- A binary product of proper maps is proper. -/
lemma IsProperMap.prodMap {g : Z → W} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (Prod.map f g) := by
  simp_rw [isProperMap_iff_ultrafilter] at hf hg ⊢
  constructor
  -- Continuity is clear.
  · exact hf.1.prodMap hg.1
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

@[deprecated (since := "2024-10-06")] alias IsProperMap.prod_map := IsProperMap.prodMap

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
proper map when the codomain is compactly generated and Hausdorff. -/
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

/-- An injective and continuous function is proper if and only if it is closed. -/
lemma isProperMap_iff_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injective) :
    IsProperMap f ↔ IsClosedMap f := by
  refine ⟨fun h ↦ h.isClosedMap, fun h ↦ ?_⟩
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  exact ⟨f_cont, h, fun y ↦ (subsingleton_singleton.preimage f_inj).isCompact⟩

/-- A injective continuous and closed map is proper. -/
lemma isProperMap_of_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injective)
    (f_closed : IsClosedMap f) : IsProperMap f :=
  (isProperMap_iff_isClosedMap_of_inj f_cont f_inj).2 f_closed

/-- A homeomorphism is proper. -/
@[simp] lemma Homeomorph.isProperMap (e : X ≃ₜ Y) : IsProperMap e :=
  isProperMap_of_isClosedMap_of_inj e.continuous e.injective e.isClosedMap

protected lemma IsHomeomorph.isProperMap (hf : IsHomeomorph f) : IsProperMap f :=
  isProperMap_of_isClosedMap_of_inj hf.continuous hf.injective hf.isClosedMap

/-- The identity is proper. -/
@[simp] lemma isProperMap_id : IsProperMap (id : X → X) := IsHomeomorph.id.isProperMap

/-- A closed embedding is proper. -/
lemma isProperMap_of_isClosedEmbedding (hf : IsClosedEmbedding f) : IsProperMap f :=
  isProperMap_of_isClosedMap_of_inj hf.continuous hf.inj hf.isClosedMap

/-- The coercion from a closed subset is proper. -/
lemma isProperMap_subtype_val_of_closed {U : Set X} (hU : IsClosed U) : IsProperMap ((↑) : U → X) :=
  isProperMap_of_isClosedEmbedding hU.isClosedEmbedding_subtype_val

/-- The restriction of a proper map to a closed subset is proper. -/
lemma isProperMap_restr_of_proper_of_closed {U : Set X} (hf : IsProperMap f) (hU : IsClosed U) :
    IsProperMap (fun x : U ↦ f x) :=
  IsProperMap.comp (isProperMap_subtype_val_of_closed hU) hf

/-- The range of a proper map is closed. -/
lemma IsProperMap.isClosed_range (hf : IsProperMap f) : IsClosed (range f) :=
  hf.isClosedMap.isClosed_range

@[deprecated (since := "2024-05-08")] alias IsProperMap.closed_range := IsProperMap.isClosed_range

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

/-- A proper map `f : X → Y` is **universally closed**: for any topological space `Z`, the map
`Prod.map f id : X × Z → Y × Z` is closed. We will prove in `isProperMap_iff_universally_closed`
that proper maps are exactly continuous maps which have this property, but this result should be
easier to use because it allows `Z` to live in any universe. -/
theorem IsProperMap.universally_closed (Z) [TopologicalSpace Z] (h : IsProperMap f) :
    IsClosedMap (Prod.map f id : X × Z → Y × Z) :=
  -- `f × id` is proper as a product of proper maps, hence closed.
  (h.prodMap isProperMap_id).isClosedMap

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
        (Eventually.of_forall fun x ↦ ⟨⟨x, pure x⟩, subset_closure rfl, rfl⟩)
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
