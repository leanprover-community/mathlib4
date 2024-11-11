/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Bhavik Mehta, Daniel Weber
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic

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

open Set Filter Function Topology

variable {X Y : Type*} [TopologicalSpace Y] {f : X → Y}

section cofinite_cocompact

lemma tendsto_cofinite_cocompact_iff :
    Tendsto f cofinite (cocompact _) ↔ ∀ K, IsCompact K → Set.Finite (f ⁻¹' K) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  refine forall₂_congr (fun K _ ↦ ?_)
  simp only [mem_compl_iff, eventually_cofinite, not_not, preimage]

variable [TopologicalSpace X]

lemma Continuous.discrete_of_tendsto_cofinite_cocompact [T1Space X] [WeaklyLocallyCompactSpace Y]
    (hf' : Continuous f) (hf : Tendsto f cofinite (cocompact _)) :
    DiscreteTopology X := by
  refine singletons_open_iff_discrete.mp (fun x ↦ ?_)
  obtain ⟨K : Set Y, hK : IsCompact K, hK' : K ∈ 𝓝 (f x)⟩ := exists_compact_mem_nhds (f x)
  obtain ⟨U : Set Y, hU₁ : U ⊆ K, hU₂ : IsOpen U, hU₃ : f x ∈ U⟩ := mem_nhds_iff.mp hK'
  have hU₄ : Set.Finite (f⁻¹' U) :=
    Finite.subset (tendsto_cofinite_cocompact_iff.mp hf K hK) (preimage_mono hU₁)
  exact isOpen_singleton_of_finite_mem_nhds _ ((hU₂.preimage hf').mem_nhds hU₃) hU₄

lemma tendsto_cofinite_cocompact_of_discrete [DiscreteTopology X]
    (hf : Tendsto f (cocompact _) (cocompact _)) :
    Tendsto f cofinite (cocompact _) := by
  convert hf
  rw [cocompact_eq_cofinite X]

lemma IsClosed.tendsto_coe_cofinite_of_discreteTopology
    {s : Set X} (hs : IsClosed s) (_hs' : DiscreteTopology s) :
    Tendsto ((↑) : s → X) cofinite (cocompact _) :=
  tendsto_cofinite_cocompact_of_discrete hs.isClosedEmbedding_subtypeVal.tendsto_cocompact

lemma IsClosed.tendsto_coe_cofinite_iff [T1Space X] [WeaklyLocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) :
    Tendsto ((↑) : s → X) cofinite (cocompact _) ↔ DiscreteTopology s :=
  ⟨continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact,
   fun _ ↦ hs.tendsto_coe_cofinite_of_discreteTopology inferInstance⟩

end cofinite_cocompact

section codiscrete_filter

variable [TopologicalSpace X]

/-- Criterion for a subset `S ⊆ X` to be closed and discrete in terms of the punctured
neighbourhood filter at an arbitrary point of `X`. (Compare `discreteTopology_subtype_iff`.) -/
theorem isClosed_and_discrete_iff {S : Set X} :
    IsClosed S ∧ DiscreteTopology S ↔ ∀ x, Disjoint (𝓝[≠] x) (𝓟 S) := by
  rw [discreteTopology_subtype_iff, isClosed_iff_clusterPt, ← forall_and]
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

lemma mem_codiscreteWithin_accPt {S T : Set X} :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, ¬AccPt x (𝓟 (T \ S)) := by
  simp only [mem_codiscreteWithin, disjoint_iff, AccPt, not_neBot]

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
    S ∈ codiscrete X ↔ IsOpen S ∧ DiscreteTopology ↑Sᶜ := by
  rw [mem_codiscrete, ← isClosed_compl_iff, isClosed_and_discrete_iff]

lemma mem_codiscrete_subtype_iff_mem_codiscreteWithin {S : Set X} {U : Set S} :
    U ∈ codiscrete S ↔ (↑) '' U ∈ codiscreteWithin S := by
  simp [mem_codiscrete, disjoint_principal_right, compl_compl, Subtype.forall,
    mem_codiscreteWithin]
  congr! with x hx
  constructor
  · rw [nhdsWithin_subtype, mem_comap]
    rintro ⟨t, ht1, ht2⟩
    rw [mem_nhdsWithin] at ht1 ⊢
    obtain ⟨u, hu1, hu2, hu3⟩ := ht1
    refine ⟨u, hu1, hu2, fun v hv ↦ ?_⟩
    simpa using fun hv2 ↦ ⟨hv2, ht2 <| hu3 <| by simpa [hv2]⟩
  · suffices Tendsto (↑) (𝓝[≠] (⟨x, hx⟩ : S)) (𝓝[≠] x) by convert tendsto_def.mp this _; ext; simp
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      continuous_subtype_val.continuousWithinAt <| eventually_mem_nhdsWithin.mono (by simp)

end codiscrete_filter
