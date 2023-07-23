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
-/

open Filter Topology Function Set
open Prod (fst snd)

theorem IsClosedMap.image_closure_eq_of_continuous [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) :
    f '' closure s = closure (f '' s) :=
  subset_antisymm f_cont.continuousOn.image_closure (f_closed.closure_image_subset s)

theorem IsClosedMap.map_lift'_closure_eq [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (f_closed : IsClosedMap f) (f_cont : Continuous f) (F : Filter X) :
    map f (F.lift' closure) = (map f F).lift' closure := by
  rw [map_lift'_eq2 (monotone_closure Y), map_lift'_eq (monotone_closure X)]
  congr
  ext s : 1
  exact f_closed.image_closure_eq_of_continuous f_cont s

theorem IsClosedMap.mapClusterPt_iff_lift'_closure [TopologicalSpace X] [TopologicalSpace Y]
    {F : Filter X} {f : X → Y} (f_closed : IsClosedMap f) (f_cont : Continuous f) {y : Y} :
    MapClusterPt y F f ↔ ((F.lift' closure) ⊓ 𝓟 (f ⁻¹' {y})).NeBot := by
  rw [MapClusterPt, clusterPt_iff_lift'_closure', ← f_closed.map_lift'_closure_eq f_cont,
      ← comap_principal, ← map_neBot_iff f, Filter.push_pull, principal_singleton]

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  {f : X → Y}

/-- A map `f : X → Y` between two topological spaces is said to be **proper** if it is continuous
and, for all `ℱ : Filter X`, any cluster point of `map f ℱ` is the image by `f` of a cluster point
of `f`. -/
structure IsProperMap (f : X → Y) extends Continuous f : Prop where
  /-- By definition, if `f` is a proper map and `ℱ` is any filter on `X`, then any cluster point of
  `map f ℱ` is the image by `f` of some cluster point of `ℱ`. -/
  clusterPt_of_mapClusterPt :
    ∀ ⦃ℱ : Filter X⦄, ∀ ⦃y : Y⦄, MapClusterPt y ℱ f → ∃ x, f x = y ∧ ClusterPt x ℱ

/-- By definition, a proper map is continuous. -/
lemma IsProperMap.continuous (h : IsProperMap f) : Continuous f := h.toContinuous

/-- Definition of proper maps. -/
lemma isProperMap_iff_clusterPt : IsProperMap f ↔ Continuous f ∧
    ∀ ⦃ℱ : Filter X⦄, ∀ ⦃y : Y⦄, MapClusterPt y ℱ f → ∃ x, f x = y ∧ ClusterPt x ℱ :=
  ⟨fun h' ↦ ⟨h'.continuous, h'.clusterPt_of_mapClusterPt⟩, fun ⟨h, h'⟩ ↦ ⟨h, h'⟩⟩

/-- An homeomorphism is proper. -/
lemma Homeomorph.isProperMap (e : X ≃ₜ Y) : IsProperMap e := by
  rw [isProperMap_iff_clusterPt]
  refine ⟨e.continuous, fun ℱ y ↦ ?_⟩
  simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, e.comap_nhds_eq,
    ← e.coe_toEquiv, ← e.eq_symm_apply, exists_eq_left]
  exact id

/-- The identity is proper. -/
lemma isProperMap_id : IsProperMap (id : X → X) := (Homeomorph.refl X).isProperMap

/-- A proper map is closed. -/
lemma IsProperMap.isClosedMap (h : IsProperMap f) : IsClosedMap f := by
  rw [IsClosedMap_iff_clusterPt]
  intro A hA
  rw [isClosed_iff_clusterPt] at hA ⊢
  intro y hy
  rw [← map_principal] at hy
  rcases h.clusterPt_of_mapClusterPt hy with ⟨x, hxy, hx⟩
  exact ⟨x, hA x hx, hxy⟩

lemma isProperMap_iff_ultrafilter : IsProperMap f ↔ Continuous f ∧
    ∀ ⦃𝒰 : Ultrafilter X⦄, ∀ ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) → ∃ x, f x = y ∧ 𝒰 ≤ 𝓝 x := by
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

lemma IsProperMap.ultrafilter_le_nhds_of_tendsto (h : IsProperMap f) ⦃𝒰 : Ultrafilter X⦄ ⦃y : Y⦄
    (hy : Tendsto f 𝒰 (𝓝 y)) : ∃ x, f x = y ∧ 𝒰 ≤ 𝓝 x :=
  (isProperMap_iff_ultrafilter.mp h).2 hy

lemma IsProperMap.prod_map {g : Z → W} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (Prod.map f g) := by
  simp_rw [isProperMap_iff_ultrafilter] at hf hg ⊢
  constructor
  · exact hf.1.prod_map hg.1
  · intro 𝒰 ⟨y, w⟩ hyw
    simp_rw [nhds_prod_eq, tendsto_prod_iff'] at hyw
    rcases hf.2 (show Tendsto f (Ultrafilter.map fst 𝒰) (𝓝 y) by simpa using hyw.1) with
      ⟨x, hxy, hx⟩
    rcases hg.2 (show Tendsto g (Ultrafilter.map snd 𝒰) (𝓝 w) by simpa using hyw.2) with
      ⟨z, hzw, hz⟩
    refine ⟨⟨x, z⟩, Prod.ext hxy hzw, ?_⟩
    rw [nhds_prod_eq, le_prod]
    exact ⟨hx, hz⟩

lemma IsProperMap.pi_map {X Y : ι → Type _} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : (i : ι) → X i → Y i} (h : ∀ i, IsProperMap (f i)) :
    IsProperMap (fun (x : ∀ i, X i) i ↦ f i (x i)) := by
  simp_rw [isProperMap_iff_ultrafilter] at h ⊢
  constructor
  · exact continuous_pi fun i ↦ (h i).1.comp (continuous_apply i)
  · intro 𝒰 y hy
    have : ∀ i, Tendsto (f i) (Ultrafilter.map (eval i) 𝒰) (𝓝 (y i)) :=
      by simpa [tendsto_pi_nhds] using hy
    choose x hxy hx using fun i ↦ (h i).2 (this i)
    refine ⟨x, funext hxy, ?_⟩
    rwa [nhds_pi, le_pi]

lemma IsProperMap.isCompact_preimage (h : IsProperMap f) {K : Set Y} (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  rw [← comap_principal, ← map_le_iff_le_comap, ← Ultrafilter.coe_map] at h𝒰
  rcases hK.ultrafilter_le_nhds _ h𝒰 with ⟨y, hyK, hy⟩
  rcases h.ultrafilter_le_nhds_of_tendsto hy with ⟨x, rfl, hx⟩
  exact ⟨x, hyK, hx⟩

theorem isProperMap_iff_isClosedMap_and_compact_fibers :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ ∀ y, IsCompact (f ⁻¹' {y}) := by
  constructor <;> intro H
  -- Note: In Bourbaki, the direct implication is proved by going through universally closed maps.
  -- We could do the same (using a `TFAE` cycle) but proving it directly from
  -- `IsProperMap.isCompact_preimage` is nice enough already so we don't bother with that.
  · exact ⟨H.continuous, H.isClosedMap, fun y ↦ H.isCompact_preimage isCompact_singleton⟩
  · rw [isProperMap_iff_clusterPt]
    refine ⟨H.1, fun 𝓕 y hy ↦ ?_⟩
    rw [H.2.1.mapClusterPt_iff_lift'_closure H.1] at hy
    rcases H.2.2 y (f := Filter.lift' 𝓕 closure ⊓ 𝓟 (f ⁻¹' {y})) inf_le_right with ⟨x, hxy, hx⟩
    refine ⟨x, hxy, ?_⟩
    rw [← clusterPt_lift'_closure_iff]
    exact hx.mono inf_le_left

theorem isProperMap_iff_isClosedMap_and_tendsto_cofinite [T1Space Y] :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ Tendsto f (cocompact X) cofinite := by
  simp_rw [isProperMap_iff_isClosedMap_and_compact_fibers, Tendsto,
    le_cofinite_iff_compl_singleton_mem, mem_map, preimage_compl]
  refine and_congr_right fun f_cont ↦ and_congr_right fun _ ↦
    ⟨fun H y ↦ (H y).compl_mem_cocompact, fun H y ↦ ?_⟩
  rcases mem_cocompact.mp (H y) with ⟨K, hK, hKy⟩
  exact isCompact_of_isClosed_subset hK (isClosed_singleton.preimage f_cont)
    (compl_le_compl_iff_le.mp hKy)

theorem isProperMap_iff_isCompact_preimage [T2Space Y] [LocallyCompactSpace Y] :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃K⦄, IsCompact K → IsCompact (f ⁻¹' K) := by
  constructor <;> intro H
  · exact ⟨H.continuous, fun K hK ↦ H.isCompact_preimage hK⟩
  · rw [isProperMap_iff_ultrafilter]
    refine ⟨H.1, fun 𝒰 y hy ↦ ?_⟩
    rcases exists_compact_mem_nhds y with ⟨K, hK, hKy⟩
    have : 𝒰 ≤ 𝓟 (f ⁻¹' K) := by
      simpa only [← comap_principal, ← tendsto_iff_comap] using
        hy.mono_right (le_principal_iff.mpr hKy)
    rcases (H.2 hK).ultrafilter_le_nhds _ this with ⟨x, -, hx⟩
    rw [← tendsto_id'] at hx
    refine ⟨x, tendsto_nhds_unique ((H.1.tendsto _).comp hx) hy, hx⟩

theorem isProperMap_iff_tendsto_cocompact [T2Space Y] [LocallyCompactSpace Y] :
    IsProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y) := by
  simp_rw [isProperMap_iff_isCompact_preimage, hasBasis_cocompact.tendsto_right_iff,
    ← mem_preimage, eventually_mem_set, preimage_compl]
  refine and_congr_right fun f_cont ↦
    ⟨fun H K hK ↦ (H hK).compl_mem_cocompact, fun H K hK ↦ ?_⟩
  rcases mem_cocompact.mp (H K hK) with ⟨K', hK', hK'y⟩
  exact isCompact_of_isClosed_subset hK' (hK.isClosed.preimage f_cont)
    (compl_le_compl_iff_le.mp hK'y)

theorem IsProperMap.universally_closed (Z) [TopologicalSpace Z] (h : IsProperMap f) :
    IsClosedMap (Prod.map f id : X × Z → Y × Z) :=
  (h.prod_map isProperMap_id).isClosedMap

theorem isProperMap_iff_isClosedMap_filter {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap
      (Prod.map f id : X × Filter X → Y × Filter X) := by
  constructor <;> intro H
  · exact ⟨H.continuous, H.universally_closed _⟩
  · rw [isProperMap_iff_ultrafilter]
    refine ⟨H.1, fun 𝒰 y hy ↦ ?_⟩
    let F : Set (X × Filter X) := closure {xℱ | xℱ.2 = pure xℱ.1}
    have := H.2 F isClosed_closure
    have : (y, ↑𝒰) ∈ Prod.map f id '' F :=
      this.mem_of_tendsto (hy.prod_mk_nhds (Filter.tendsto_pure_self (𝒰 : Filter X)))
        (eventually_of_forall fun x ↦ ⟨⟨x, pure x⟩, subset_closure rfl, rfl⟩)
    rcases this with ⟨⟨x, _⟩, hx, ⟨_, _⟩⟩
    refine ⟨x, rfl, fun U hU ↦ Ultrafilter.compl_not_mem_iff.mp fun hUc ↦ ?_⟩
    rw [mem_closure_iff_nhds] at hx
    rcases hx (U ×ˢ {𝒢 | Uᶜ ∈ 𝒢}) (prod_mem_nhds hU (isOpen_setOf_mem.mem_nhds hUc)) with
      ⟨⟨y, 𝒢⟩, ⟨⟨hy : y ∈ U, hy' : Uᶜ ∈ 𝒢⟩, rfl : 𝒢 = pure y⟩⟩
    exact hy' hy

theorem isProperMap_iff_isClosedMap_ultrafilter {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap
      (Prod.map f id : X × Ultrafilter X → Y × Ultrafilter X) := by
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

theorem isProperMap_iff_universally_closed {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ ∀ (Z : Type u) [TopologicalSpace Z],
      IsClosedMap (Prod.map f id : X × Z → Y × Z) := by
  constructor <;> intro H
  · exact ⟨H.continuous, fun Z ↦ H.universally_closed _⟩
  · rw [isProperMap_iff_isClosedMap_ultrafilter]
    exact ⟨H.1, H.2 _⟩
