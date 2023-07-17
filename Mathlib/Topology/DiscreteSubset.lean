/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Bhavik Mehta
-/
import Mathlib.Topology.SubsetProperties
import Mathlib.Topology.Separation

/-!
# Discrete subsets of topological spaces

Given a topological space `X` together with a subset `s ⊆ X`, there are two distinct concepts of
"discreteness" which may hold. These are:
  (i) Every point of `s` is isolated (i.e., the subset topology induced on `s` is the discrete
      topology).
 (ii) Every compact subset of `X` meets `s` only finitely often (i.e., the inclusion map `s → X`
      tends to the cocompact filter along the cofinite filter on `s`).

When `s` is closed, the two conditions are equivalent provided `X` is locally compact and T1,
see `IsClosed.tendsto_coe_cofinite_iff`. In general however (i) and (ii) are different and it is
(ii) that is most useful, see e.g., `Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite`.

## Main definitions

 * `tendsto_cofinite_cocompact_iff`:
 * `IsClosed.tendsto_coe_cofinite_iff`:

-/

open Set Filter Function Topology

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- See also `tendsto_cofinite_cocompact_iff'` for a useful variant when `f` is injective. -/
lemma tendsto_cofinite_cocompact_iff :
    Tendsto f cofinite (cocompact _) ↔ ∀ K, IsCompact K → Set.Finite (f ⁻¹' K) := by
  refine' ⟨fun h K hK ↦ _, fun h U hU ↦ _⟩
  · replace h : Kᶜ ∈ map f cofinite := h hK.compl_mem_cocompact
    rwa [mem_map, mem_cofinite, preimage_compl, compl_compl] at h
  · obtain ⟨t, ht : IsCompact t, ht' : Uᶜ ⊆ t⟩ := mem_cocompact'.mp hU
    replace h : Set.Finite (f ⁻¹' Uᶜ) := (h t ht).subset (preimage_mono ht')
    rwa [mem_map, mem_cofinite, ← preimage_compl]

lemma Continuous.discrete_of_tendsto_cofinite_cocompact [T1Space X] [LocallyCompactSpace Y]
    (hf' : Continuous f) (hf : Tendsto f cofinite (cocompact _)) :
    DiscreteTopology X := by
  refine' singletons_open_iff_discrete.mp (fun x ↦ _)
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

lemma IsClosed.tendsto_coe_cofinite_iff [T1Space X] [LocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) :
    Tendsto ((↑) : s → X) cofinite (cocompact _) ↔ DiscreteTopology s :=
  ⟨continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact,
   fun _ ↦ tendsto_cofinite_cocompact_of_discrete hs.closedEmbedding_subtype_val.tendsto_cocompact⟩
