/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Bhavik Mehta
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation

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

In a topological space the sets which are open with discrete complement form a filter. We
formalise this as `Filter.codiscrete`.

-/

open Set Filter Function Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

section cofinite_cocompact

lemma tendsto_cofinite_cocompact_iff :
    Tendsto f cofinite (cocompact _) ↔ ∀ K, IsCompact K → Set.Finite (f ⁻¹' K) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  refine forall₂_congr (fun K _ ↦ ?_)
  simp only [mem_compl_iff, eventually_cofinite, not_not, preimage]

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
  tendsto_cofinite_cocompact_of_discrete hs.closedEmbedding_subtype_val.tendsto_cocompact

lemma IsClosed.tendsto_coe_cofinite_iff [T1Space X] [WeaklyLocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) :
    Tendsto ((↑) : s → X) cofinite (cocompact _) ↔ DiscreteTopology s :=
  ⟨continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact,
   fun _ ↦ hs.tendsto_coe_cofinite_of_discreteTopology inferInstance⟩

end cofinite_cocompact

section codiscrete_filter

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

/-- In any topological space, the open sets with with discrete complement form a filter. -/
def Filter.codiscrete (X : Type*) [TopologicalSpace X] : Filter X where
  sets := {U | IsOpen U ∧ DiscreteTopology ↑Uᶜ}
  univ_sets := ⟨isOpen_univ, compl_univ.symm ▸ Subsingleton.discreteTopology⟩
  sets_of_superset := by
    intro U V hU hV
    simp_rw [← isClosed_compl_iff, isClosed_and_discrete_iff] at hU ⊢
    exact fun x ↦ (hU x).mono_right (principal_mono.mpr <| compl_subset_compl.mpr hV)
  inter_sets := by
    intro U V hU hV
    simp_rw [← isClosed_compl_iff, isClosed_and_discrete_iff] at hU hV ⊢
    exact fun x ↦ compl_inter U V ▸ sup_principal ▸ disjoint_sup_right.mpr ⟨hU x, hV x⟩

end codiscrete_filter
