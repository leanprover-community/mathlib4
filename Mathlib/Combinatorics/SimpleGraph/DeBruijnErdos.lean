/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Topology.Compactness.Compact

/-!
# Combinatorial compactness and the Rado selection lemma

This file proves the Rado selection lemma in a number of variants, as an application of compactness
to combinatorics. Many (though not all) uses of compactness arguments in combinatorics can be 
formulated using this lemma.

We give four versions, depending on whether the "partial" functions are defined locally or globally,
and whether we use `Finset` or `Set.Finite`. The precise formulation of the lemma is therefore
`Finset.rado_selection_subtype` or `Set.Finite.rado_selection_subtype`, but the versions avoiding
subtypes are easier to prove and often easier to apply, so they are provided too.
-/

/--
Given a (dependent) function `g s : (a : α) → β a` for each finset `s` of `α`, provided that 
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Finset.rado_selection {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Finset α) → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α, ∃ t : Finset α, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x := by
  classical
  let instTop (a : α) : TopologicalSpace (β a) := ⊥
  have instDiscr (a : α) : DiscreteTopology (β a) := discreteTopology_bot _
  let e (s : Finset α) : Set ((a : α) → β a) := {f | ∃ t, s ⊆ t ∧ ∀ x ∈ s, f x = g t x}
  let restr (s : Finset α) : ((a : α) → β a) → (a : s) → β a := fun f a ↦ f a
  have hrestr (s : Finset α) : Continuous (restr s) := by fun_prop
  have (s : Finset α) : restr s ⁻¹' {f | ∃ t, s ⊆ t ∧ ∀ x, f x = g t x} = e s := by simp [e, restr]
  have he' (s : Finset α) : IsClosed (e s) := by
    rw [← this]
    exact (isClosed_discrete _).preimage (hrestr _)
  have he'' (B : Finset (Finset α)) : (⋂ i ∈ B, e i).Nonempty := by
    refine ⟨g (B.biUnion id), ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq, e]
    intro i hi
    exact ⟨_, Finset.subset_biUnion_of_mem id hi, by simp⟩
  simpa using CompactSpace.iInter_nonempty he' he''

/--
Given a (dependent) function `g s : (a : s) → β a` for each finset `s` of `α`, provided that 
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Finset.rado_selection_subtype {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Finset α) → (a : s) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α,
      ∃ (t : Finset α) (hst : s ⊆ t), ∀ x : s, χ x = g t (Set.inclusion hst x) := by
  classical
  have (a : α) : Nonempty (β a) := ⟨g {a} ⟨a, by simp⟩⟩
  let g' (s) (a : α) : β a := if ha : a ∈ s then g s ⟨a, ha⟩ else Classical.arbitrary (β a)
  have hg (s : Finset α) (x : s) : g s x = g' s x := by simp [g']
  simpa [hg] using Finset.rado_selection g'

/--
Given a (dependent) function `g s : (a : α) → β a` for each finite set `s` of `α`, provided that 
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Set.Finite.rado_selection {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Set α) → s.Finite → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Set α, s.Finite →
      ∃ (t : Set α) (ht : t.Finite), s ⊆ t ∧ ∀ x ∈ s, χ x = g t ht x := by
  obtain ⟨χ, hχ⟩ := Finset.rado_selection (fun s ↦ g s s.finite_toSet)
  refine ⟨χ, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, ht'⟩ := hχ hs.toFinset
  exact ⟨t, by simp_all⟩

/--
Given a (dependent) function `g s : (a : s) → β a` for each finite set `s` of `α`, provided that 
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Set.Finite.rado_selection_subtype {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Set α) → s.Finite → (a : s) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Set α, s.Finite →
      ∃ (t : Set α) (ht : t.Finite) (hst : s ⊆ t), ∀ x : s, χ x = g t ht (Set.inclusion hst x) := by
  classical
  obtain ⟨χ, hχ⟩ := Finset.rado_selection_subtype (β := β) (fun s ↦ g s s.finite_toSet)
  refine ⟨χ, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, hst⟩ := hχ hs.toFinset
  simp only [Set.Finite.toFinset_subset] at ht
  exact ⟨t, by simp_all⟩

/--
Given a graph homomorphism from every finite subgraph of `G` to a finite graph `F`, we can find
a graph homomorphism from (the entirety of) `G` to `F`.
-/
theorem nonempty_hom_of_forall_finite_subgraph_hom {V W : Type*} [Finite W]
    {G : SimpleGraph V} {F : SimpleGraph W}
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe →g F) : Nonempty (G →g F) := by
  have := G.toSubgraph
  let g : (s : Set V) → s.Finite → s → W := fun s hs ↦ h (SimpleGraph.Subgraph.induce ⊤ s) hs
  obtain ⟨χ, hχ⟩ := Set.Finite.rado_selection_subtype (β := fun _ ↦ W) g
  refine ⟨⟨χ, ?_⟩⟩
  intro a b hab
  let a' : (G.subgraphOfAdj hab).verts := ⟨a, by simp⟩
  let b' : (G.subgraphOfAdj hab).verts := ⟨b, by simp⟩
  have hab' : (G.subgraphOfAdj hab).Adj a' b' := by simp [a', b']
  change F.Adj (χ a') (χ b')
  obtain ⟨H, hHfin, hHsub, hHeq⟩ := hχ (G.subgraphOfAdj hab).verts (by simp)
  rw [hHeq, hHeq]
  simp only [SimpleGraph.subgraphOfAdj_verts, SimpleGraph.Subgraph.induce_verts, g]
  apply (h ((⊤ : G.Subgraph).induce H) hHfin).map_adj
  simp only [SimpleGraph.subgraphOfAdj_verts, Set.insert_subset_iff,
    Set.singleton_subset_iff] at hHsub
  simp_all [a', b']

/--
Given a finite colouring of every finite subgraph of a graph `G`, we can find a colouring of `G`
with the same colouring set.
-/
theorem deBruijn_erdos {α β : Type*} (G : SimpleGraph α) [Finite β]
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe.Coloring β) : Nonempty (G.Coloring β) :=
  nonempty_hom_of_forall_finite_subgraph_hom h
