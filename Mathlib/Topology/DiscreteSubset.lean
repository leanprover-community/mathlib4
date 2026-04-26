/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Bhavik Mehta, Daniel Weber, Stefan Kebekus
-/
module

public import Mathlib.Tactic.TautoSet
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Set.Subset
public import Mathlib.Topology.Separation.Basic

/-!
# Discrete subsets of topological spaces

This file contains various additional properties of discrete subsets of topological spaces.

## Discreteness and compact sets

Given a topological space `X` together with a subset `s ⊆ X`, there are two distinct concepts of
"discreteness" which may hold. These are:
  (i) Every point of `s` is isolated (i.e., the subset topology induced on `s` is the discrete
      topology).
 (ii) Every compact subset of `X` meets `s` only finitely often (i.e., the inclusion map `s → X`
      tends to the cocompact filter along the cofinite filter on `s`).

When `s` is closed, the two conditions are equivalent provided `X` is locally compact and T1,
see `IsClosed.tendsto_coe_cofinite_iff`.

### Main statements

* `tendsto_cofinite_cocompact_iff`:
* `IsClosed.tendsto_coe_cofinite_iff`:

## Co-discrete open sets

We define the filter `Filter.codiscreteWithin S`, which is the supremum of all `𝓝[S \ {x}] x`.
This is the filter of all open codiscrete sets within S. We also define `Filter.codiscrete` as
`Filter.codiscreteWithin univ`, which is the filter of all open codiscrete sets in the space.

-/

@[expose] public section

open Set Filter Function Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s : Set X}

theorem discreteTopology_subtype_iff {S : Set Y} :
    DiscreteTopology S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]

theorem isDiscrete_iff_nhdsNE {S : Set Y} :
    IsDiscrete S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff]

/-- If a subset of a topological space has no accumulation points,
then it carries the discrete topology. -/
lemma discreteTopology_of_noAccPts {X : Type*} [TopologicalSpace X] {E : Set X}
    (h : ∀ x ∈ E, ¬ AccPt x (𝓟 E)) : DiscreteTopology E := by
  simpa [discreteTopology_subtype_iff, AccPt] using h

lemma discreteTopology_subtype_iff' {S : Set Y} :
    DiscreteTopology S ↔ ∀ y ∈ S, ∃ U : Set Y, IsOpen U ∧ U ∩ S = {y} := by
  simp [discreteTopology_iff_isOpen_singleton, isOpen_induced_iff, Set.ext_iff]
  grind

theorem isDiscrete_iff_forall_exists_isOpen {S : Set Y} :
    IsDiscrete S ↔ ∀ y ∈ S, ∃ U, IsOpen U ∧ U ∩ S = {y} := by
  rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff']

lemma Set.Subsingleton.isDiscrete (hs : s.Subsingleton) : IsDiscrete s :=
  have : Subsingleton s := (Set.subsingleton_coe s).mpr hs
  ⟨inferInstance⟩

lemma isDiscrete_iff_nhdsWithin : IsDiscrete s ↔ ∀ x ∈ s, 𝓝[s] x = pure x := by
  simp [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure, nhds_induced,
    ← (Filter.map_injective Subtype.val_injective).eq_iff,
    Filter.map_comap, nhdsWithin]

protected alias ⟨IsDiscrete.nhdsWithin, _⟩ := isDiscrete_iff_nhdsWithin

lemma IsDiscrete.of_nhdsWithin (H : ∀ x ∈ s, 𝓝[s] x ≤ pure x) : IsDiscrete s :=
  isDiscrete_iff_nhdsWithin.mpr fun x hx ↦ (H x hx).antisymm (pure_le_nhdsWithin hx)

lemma isDiscrete_univ_iff : IsDiscrete (Set.univ : Set X) ↔ DiscreteTopology X := by
  simp [isDiscrete_iff_nhdsWithin, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure]

lemma IsDiscrete.univ [DiscreteTopology X] : IsDiscrete (Set.univ : Set X) := by
  rwa [isDiscrete_univ_iff]

lemma IsDiscrete.image_of_isOpenMap (hs : IsDiscrete s) (hf : IsOpenMap f)
    (hf' : Function.Injective f) : IsDiscrete (f '' s) := by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pure, ← hs.nhdsWithin x hx, nhdsWithin, nhdsWithin, map_inf hf', map_principal]
  grw [hf.nhds_le x]

lemma IsDiscrete.image_of_isOpenMap_of_isOpen (hs : IsDiscrete s) (hf : IsOpenMap f)
    (hs' : IsOpen s) : IsDiscrete (f '' s) := by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [(hf _ hs').nhdsWithin_eq ⟨x, hx, rfl⟩, ← map_pure, ← hs.nhdsWithin x hx, hs'.nhdsWithin_eq hx]
  exact hf.nhds_le x

lemma IsOpenMap.isDiscrete_range [DiscreteTopology X] (hf : IsOpenMap f) :
    IsDiscrete (Set.range f) := by
  simpa using IsDiscrete.univ.image_of_isOpenMap_of_isOpen hf isOpen_univ

lemma IsDiscrete.image (hs : IsDiscrete s) (hf : IsInducing f) : IsDiscrete (f '' s) := by
  simp_all [isDiscrete_iff_nhdsWithin, ← hf.map_nhdsWithin_eq s]

lemma IsInducing.isDiscrete_range [DiscreteTopology X] (hf : IsInducing f) :
    IsDiscrete (Set.range f) := by
  simpa using IsDiscrete.univ.image hf

@[deprecated (since := "2026-03-30")] alias
IsEmbedding.isDiscrete_range := IsInducing.isDiscrete_range

lemma IsDiscrete.preimage {s : Set Y} (hs : IsDiscrete s)
    (hf : ContinuousOn f (f ⁻¹' s)) (hf' : Function.Injective f) :
    IsDiscrete (f ⁻¹' s) := by
  refine .of_nhdsWithin fun x hx ↦ ?_
  rw [← map_le_map_iff hf', map_pure, ← hs.nhdsWithin _ hx, ← Tendsto]
  exact (hf.continuousWithinAt hx).tendsto_nhdsWithin (Set.mapsTo_preimage _ _)

/-- If `f` is continuous with discrete fibers, then the preimage of discrete sets are discrete. -/
lemma IsDiscrete.preimage' {s : Set Y} (hs : IsDiscrete s)
    (hf : ContinuousOn f (f ⁻¹' s))
    (H : ∀ x, IsDiscrete (f ⁻¹' {x})) : IsDiscrete (f ⁻¹' s) := by
  refine .of_nhdsWithin fun x hx ↦ ?_
  have h := ((H (f x)).nhdsWithin _ rfl).le
  grw [nhdsWithin, ← comap_pure, ← hs.nhdsWithin _ hx, ← (hf.continuousWithinAt hx
    |>.tendsto_nhdsWithin fun _ ↦ by exact id).le_comap, inf_eq_right.mpr nhdsWithin_le_nhds] at h
  exact h

lemma IsDiscrete.eq_of_specializes (hs : IsDiscrete s)
    {a b : X} (hab : a ⤳ b) (ha : a ∈ s) (hb : b ∈ s) : a = b := by
  letI := hs.1
  simpa only [← Topology.IsInducing.subtypeVal.specializes_iff, hab, Subtype.mk.injEq,
    true_iff] using specializes_iff_eq (X := s) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)

section cofinite_cocompact

omit [TopologicalSpace X] in
lemma tendsto_cofinite_cocompact_iff :
    Tendsto f cofinite (cocompact _) ↔ ∀ K, IsCompact K → Set.Finite (f ⁻¹' K) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  refine forall₂_congr (fun K _ ↦ ?_)
  simp only [mem_compl_iff, eventually_cofinite, not_not, preimage]

lemma Continuous.discrete_of_tendsto_cofinite_cocompact [T1Space X] [WeaklyLocallyCompactSpace Y]
    (hf' : Continuous f) (hf : Tendsto f cofinite (cocompact _)) :
    DiscreteTopology X := by
  refine discreteTopology_iff_isOpen_singleton.mpr (fun x ↦ ?_)
  obtain ⟨K : Set Y, hK : IsCompact K, hK' : K ∈ 𝓝 (f x)⟩ := exists_compact_mem_nhds (f x)
  obtain ⟨U : Set Y, hU₁ : U ⊆ K, hU₂ : IsOpen U, hU₃ : f x ∈ U⟩ := mem_nhds_iff.mp hK'
  have hU₄ : Set.Finite (f ⁻¹' U) :=
    Finite.subset (tendsto_cofinite_cocompact_iff.mp hf K hK) (preimage_mono hU₁)
  exact isOpen_singleton_of_finite_mem_nhds _ ((hU₂.preimage hf').mem_nhds hU₃) hU₄

lemma tendsto_cofinite_cocompact_of_discrete [DiscreteTopology X]
    (hf : Tendsto f (cocompact _) (cocompact _)) :
    Tendsto f cofinite (cocompact _) := by
  convert hf
  rw [cocompact_eq_cofinite X]

lemma IsClosed.tendsto_coe_cofinite_of_isDiscrete
    {s : Set X} (hs : IsClosed s) (hs' : IsDiscrete s) :
    Tendsto ((↑) : s → X) cofinite (cocompact _) :=
  haveI := hs'.to_subtype
  tendsto_cofinite_cocompact_of_discrete hs.isClosedEmbedding_subtypeVal.tendsto_cocompact

lemma IsClosed.tendsto_coe_cofinite_iff [T1Space X] [WeaklyLocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) :
    Tendsto ((↑) : s → X) cofinite (cocompact _) ↔ IsDiscrete s :=
  ⟨fun h ↦ ⟨continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact h⟩,
   fun hs' ↦ hs.tendsto_coe_cofinite_of_isDiscrete hs'⟩

end cofinite_cocompact

section codiscrete_filter

/-- Criterion for a subset `S ⊆ X` to be closed and discrete in terms of the punctured
neighbourhood filter at an arbitrary point of `X`. (Compare `isDiscrete_iff_nhds_ne`.) -/
theorem isClosed_and_discrete_iff {S : Set X} :
    IsClosed S ∧ IsDiscrete S ↔ ∀ x, Disjoint (𝓝[≠] x) (𝓟 S) := by
  rw [isDiscrete_iff_nhdsNE, isClosed_iff_clusterPt, ← forall_and]
  congrm (∀ x, ?_)
  rw [← not_imp_not, clusterPt_iff_not_disjoint, not_not, ← disjoint_iff]
  constructor <;> intro H
  · by_cases hx : x ∈ S
    exacts [H.2 hx, (H.1 hx).mono_left nhdsWithin_le_nhds]
  · refine ⟨fun hx ↦ ?_, fun _ ↦ H⟩
    simpa [disjoint_iff, nhdsWithin, inf_assoc, hx] using H

/-- The filter of sets with no accumulation points inside a set `S : Set X`, implemented
as the supremum over all punctured neighborhoods within `S`. -/
def Filter.codiscreteWithin (S : Set X) : Filter X := ⨆ x ∈ S, 𝓝[S \ {x}] x

lemma mem_codiscreteWithin {S T : Set X} :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, Disjoint (𝓝[≠] x) (𝓟 (T \ S)) := by
  simp only [codiscreteWithin, mem_iSup, mem_nhdsWithin, disjoint_principal_right, subset_def,
    mem_diff, mem_inter_iff, mem_compl_iff]
  congr! 7 with x - u y
  tauto

/--
A set `s` is codiscrete within `U` iff `s ∪ Uᶜ` is a punctured neighborhood of every point in `U`.
-/
theorem mem_codiscreteWithin_iff_forall_mem_nhdsNE {S T : Set X} :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, S ∪ Tᶜ ∈ 𝓝[≠] x := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_diff]

lemma mem_codiscreteWithin_accPt {S T : Set X} :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, ¬AccPt x (𝓟 (T \ S)) := by
  simp only [mem_codiscreteWithin, disjoint_iff, AccPt, not_neBot]

/-- Any set is codiscrete within itself. -/
@[simp]
theorem Filter.self_mem_codiscreteWithin (U : Set X) :
    U ∈ Filter.codiscreteWithin U := by simp [mem_codiscreteWithin]

/-- If a set is codiscrete within `U`, then it is codiscrete within any subset of `U`. -/
lemma Filter.codiscreteWithin.mono {U₁ U : Set X} (hU : U₁ ⊆ U) :
    codiscreteWithin U₁ ≤ codiscreteWithin U := by
  refine (biSup_mono hU).trans <| iSup₂_mono fun _ _ ↦ ?_
  gcongr

/-- If `s` is codiscrete within `U`, then `sᶜ ∩ U` has discrete topology. -/
theorem isDiscrete_of_codiscreteWithin {U s : Set X} (h : sᶜ ∈ Filter.codiscreteWithin U) :
    IsDiscrete (s ∩ U) := by
  rw [(by simp : ((s ∩ U) : Set X) = ((sᶜ ∪ Uᶜ)ᶜ : Set X)), isDiscrete_iff_nhdsNE]
  simp_rw [← Filter.mem_iff_inf_principal_compl]
  simp_all [← Set.compl_diff, mem_codiscreteWithin]

/-- Helper lemma for `codiscreteWithin_iff_locallyFiniteComplementWithin`: A set `s` is
`codiscreteWithin U` iff every point `z ∈ U` has a punctured neighborhood that does not intersect
`U \ s`. -/
lemma codiscreteWithin_iff_locallyEmptyComplementWithin {s U : Set X} :
    s ∈ codiscreteWithin U ↔ ∀ z ∈ U, ∃ t ∈ 𝓝[≠] z, t ∩ (U \ s) = ∅ := by
  simp only [mem_codiscreteWithin, disjoint_principal_right]
  refine ⟨fun h z hz ↦ ⟨(U \ s)ᶜ, h z hz, by simp⟩, fun h z hz ↦ ?_⟩
  rw [← exists_mem_subset_iff]
  obtain ⟨t, h₁t, h₂t⟩ := h z hz
  use t, h₁t, (disjoint_iff_inter_eq_empty.mpr h₂t).subset_compl_right

/-- If `U` is closed and `s` is codiscrete within `U`, then `U \ s` is closed. -/
theorem isClosed_sdiff_of_codiscreteWithin {s U : Set X} (hs : s ∈ codiscreteWithin U)
    (hU : IsClosed U) :
    IsClosed (U \ s) := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x ∈ U
  · rw [mem_codiscreteWithin] at hs
    filter_upwards [eventually_nhdsWithin_iff.1 (disjoint_principal_right.1 (hs x h₁x))]
    intro a ha
    by_cases h₂a : a = x
    · tauto_set
    · specialize ha h₂a
      tauto_set
  · rw [eventually_iff_exists_mem]
    use Uᶜ, hU.compl_mem_nhds h₁x
    intro y hy
    tauto_set

/-- In a T1Space, punctured neighborhoods are stable under removing finite sets of points. -/
theorem nhdsNE_of_nhdsNE_sdiff_finite {X : Type*} [TopologicalSpace X] [T1Space X] {x : X}
    {U s : Set X} (hU : U ∈ 𝓝[≠] x) (hs : Finite s) :
    U \ s ∈ 𝓝[≠] x := by
  rw [mem_nhdsWithin] at hU ⊢
  obtain ⟨t, ht, h₁ts, h₂ts⟩ := hU
  use t \ (s \ {x})
  constructor
  · rw [← isClosed_compl_iff, compl_diff]
    exact s.toFinite.diff.isClosed.union (isClosed_compl_iff.2 ht)
  · tauto_set

/-- In a T1Space, a set `s` is codiscreteWithin `U` iff it has locally finite complement within `U`.
More precisely: `s` is codiscreteWithin `U` iff every point `z ∈ U` has a punctured neighborhood
intersect `U \ s` in only finitely many points. -/
theorem codiscreteWithin_iff_locallyFiniteComplementWithin [T1Space X] {s U : Set X} :
    s ∈ codiscreteWithin U ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ (U \ s)) := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  constructor
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use insert z t, insert_mem_nhds_iff.mpr h₁t
    by_cases hz : z ∈ U \ s
    · rw [inter_comm, inter_insert_of_mem hz, inter_comm, h₂t]
      simp
    · rw [inter_comm, inter_insert_of_notMem hz, inter_comm, h₂t]
      simp
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use t \ (t ∩ (U \ s)), nhdsNE_of_nhdsNE_sdiff_finite (mem_nhdsWithin_of_mem_nhds h₁t) h₂t
    simp

/-- In any topological space, the open sets with discrete complement form a filter,
defined as the supremum of all punctured neighborhoods.

See `Filter.mem_codiscrete'` for the equivalence. -/
def Filter.codiscrete (X : Type*) [TopologicalSpace X] : Filter X := codiscreteWithin Set.univ

lemma mem_codiscrete {S : Set X} :
    S ∈ codiscrete X ↔ ∀ x, Disjoint (𝓝[≠] x) (𝓟 Sᶜ) := by
  simp [codiscrete, mem_codiscreteWithin, compl_eq_univ_diff]

lemma mem_codiscrete_accPt {S : Set X} :
    S ∈ codiscrete X ↔ ∀ x, ¬AccPt x (𝓟 Sᶜ) := by
  simp only [mem_codiscrete, disjoint_iff, AccPt, not_neBot]

lemma mem_codiscrete' {S : Set X} :
    S ∈ codiscrete X ↔ IsOpen S ∧ IsDiscrete Sᶜ := by
  rw [mem_codiscrete, ← isClosed_compl_iff, isClosed_and_discrete_iff]

lemma compl_mem_codiscrete_iff {S : Set X} :
    Sᶜ ∈ codiscrete X ↔ IsClosed S ∧ DiscreteTopology ↑S := by
  rw [mem_codiscrete, compl_compl, ← isDiscrete_iff_discreteTopology, isClosed_and_discrete_iff]

lemma mem_codiscrete_subtype_iff_mem_codiscreteWithin {S : Set X} {U : Set S} :
    U ∈ codiscrete S ↔ (↑) '' U ∈ codiscreteWithin S := by
  simp only [mem_codiscrete, disjoint_principal_right, compl_compl, Subtype.forall,
    mem_codiscreteWithin]
  congr! with x hx
  constructor
  · rw [nhdsWithin_subtype, mem_comap]
    rintro ⟨t, ht1, ht2⟩
    rw [mem_nhdsWithin] at ht1 ⊢
    obtain ⟨u, hu1, hu2, hu3⟩ := ht1
    refine ⟨u, hu1, hu2, fun v hv ↦ ?_⟩
    simpa using fun hv2 ↦ ⟨hv2, ht2 <| hu3 <| by simpa [hv2]⟩
  · suffices Tendsto (↑) (𝓝[≠] (⟨x, hx⟩ : S)) (𝓝[≠] x) by
      have aux : Subtype.val ⁻¹' (S \ Subtype.val '' U)ᶜ = U := by ext; simp
      simpa [aux] using tendsto_def.mp this ((S \ Subtype.val '' U)ᶜ)
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      continuous_subtype_val.continuousWithinAt <| eventually_mem_nhdsWithin.mono (by simp)

section T1Space

variable [T1Space X]

lemma codiscrete_le_cofinite : codiscrete X ≤ cofinite := by
  intro s hs
  rw [← compl_compl s, compl_mem_codiscrete_iff]
  exact ⟨hs.isClosed, hs.isDiscrete.to_subtype⟩

lemma Set.Finite.compl_mem_codiscrete {S : Set X} (hs : S.Finite) : Sᶜ ∈ codiscrete X :=
  codiscrete_le_cofinite (by simpa)

lemma Set.Infinite.of_accPt {S : Set X} {x : X} (h : AccPt x (𝓟 S)) : S.Infinite := by
  intro hs
  have := hs.compl_mem_codiscrete
  rw [mem_codiscrete_accPt, compl_compl] at this
  exact this _ h

end T1Space

end codiscrete_filter

section discrete_union

/-- The union of two discrete closed subsets is discrete. -/
theorem discreteTopology_union {S T : Set X} (hs : DiscreteTopology S) (ht : DiscreteTopology T)
    (hs' : IsClosed S) (ht' : IsClosed T) : DiscreteTopology ↑(S ∪ T) := by
  suffices (S ∪ T)ᶜ ∈ codiscrete X from compl_mem_codiscrete_iff.mp this |>.2
  have hS : Sᶜ ∈ codiscrete X := by simpa [compl_mem_codiscrete_iff] using ⟨hs', hs⟩
  have hT : Tᶜ ∈ codiscrete X := by simpa [compl_mem_codiscrete_iff] using ⟨ht', ht⟩
  simpa using inter_mem hS hT

/-- The union of finitely many discrete closed subsets is discrete. -/
theorem discreteTopology_biUnion_finset {ι : Type*} {I : Finset ι} {s : ι → Set X}
    (hs : ∀ i ∈ I, DiscreteTopology (s i)) (hs' : ∀ i ∈ I, IsClosed (s i)) :
    DiscreteTopology (⋃ i ∈ I, s i) := by
  suffices (⋃ i ∈ I, s i)ᶜ ∈ codiscrete X from (compl_mem_codiscrete_iff.mp this).2
  simpa [biInter_finset_mem I] using fun i hi ↦ compl_mem_codiscrete_iff.mpr ⟨hs' i hi, hs i hi⟩

/-- The union of finitely many discrete closed subsets is discrete. -/
theorem discreteTopology_iUnion_finite {ι : Type*} [Finite ι] {s : ι → Set X}
    (hs : ∀ i, DiscreteTopology (s i)) (hs' : ∀ i, IsClosed (s i)) :
    DiscreteTopology (⋃ i, s i) := by
  have := Fintype.ofFinite ι
  convert discreteTopology_biUnion_finset (I := .univ) (fun i _ ↦ hs i) (fun i _ ↦ hs' i) <;>
    simp

@[deprecated (since := "2025-11-28")]
alias discreteTopology_iUnion_fintype := discreteTopology_iUnion_finite

end discrete_union
