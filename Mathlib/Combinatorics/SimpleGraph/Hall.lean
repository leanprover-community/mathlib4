/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Hall's Marriage Theorem

This file derives Hall's Marriage Theorem for bipartite graphs from the combinatorial formulation in
`Mathlib/Combinatorics/Hall/Basic.lean`.

## Main statements

* `SimpleGraph.exists_IsMatching_of_forall_ncard_le`: Hall's marriage theorem for a matching for a
  matching on a single partition of a bipartite graph.
* `SimpleGraph.exists_IsPerfectMatching_of_forall_ncard_le`: Hall's marriage theorem for a perfect
  matching on a bipartite graph.

## Tags

Hall's Marriage Theorem
-/

open Function

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private
abbrev hall_subgraph {p : Set V} [DecidablePred (· ∈ p)] (f : p → V)
    (h : ∀ x : V, (h : x ∈ p) → f ⟨x, h⟩ ∉ p)
    (h₂ : ∀ x : V, (h : x ∈ p) → G.Adj x (f ⟨x, h⟩)) : Subgraph G where
  verts := p ∪ Set.range f
  Adj v w :=
    if h : v ∈ p then f ⟨v, h⟩ = w
    else if h : w ∈ p then f ⟨w, h⟩ = v
    else False
  adj_sub {v w} h := by
    repeat' split at h
    · have := h₂ v (by assumption)
      rwa [← h]
    · have := h₂ w (by assumption) |>.symm
      rwa [← h]
    · contradiction
  edge_vert {v w} := by grind
  symm {x y} := by grind

variable [DecidableEq V] [G.LocallyFinite] {p₁ p₂ : Set V}

/-- This is the version of **Hall's marriage theorem** for bipartite graphs that finds a matching
for a single partition given that the neighborhood-condition only holds for elements of that
partition. -/
theorem exists_IsMatching_of_forall_ncard_le [DecidablePred (· ∈ p₁)] (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : Subgraph G, p₁ ⊆ M.verts ∧ M.IsMatching := by
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun (x : p₁) ↦ G.neighborFinset x) |>.mp fun s ↦ by
    have := h₂ (s.image Subtype.val) (by simp)
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ Subtype.val_injective] at this
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  have (x : V) (h : x ∈ p₁) : f ⟨x, h⟩ ∉ p₁ := h₁.disjoint |>.notMem_of_mem_right <|
    isBipartiteWith_neighborSet_subset h₁ h <| Set.mem_toFinset.mp <| hf₂ ⟨x, h⟩
  use hall_subgraph f this (fun v h ↦ G.mem_neighborFinset _ _ |>.mp (hf₂ ⟨v, by assumption⟩))
  refine ⟨by simp, fun v hv ↦ ?_⟩
  simp only [Set.mem_union, Set.mem_range, Subtype.exists] at hv ⊢
  rcases hv with h' | ⟨x, hx₁, hx₂⟩
  · exact ⟨f ⟨v, h'⟩, by simp_all⟩
  · use x
    have := hx₂ ▸ (this x hx₁)
    simp only [this, ↓reduceDIte, hx₁, hx₂, dite_else_false, forall_exists_index, true_and]
    exact fun _ _ k ↦ Subtype.ext_iff_val.mp <| hf₁ (hx₂ ▸ k)

private
lemma union_eq_set_univ_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) : p₁ ∪ p₂ = Set.univ := by
  obtain ⟨f, _, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun x ↦ G.neighborFinset x) |>.mp fun s ↦ by
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
  have := hf₂ x
  have := G.mem_neighborFinset _ _ |>.mp (hf₂ x)
  have := h₁.mem_of_adj <| G.mem_neighborFinset _ _ |>.mp (hf₂ x)
  grind

private
lemma exists_bijective_of_forall_ncard_le [DecidablePred (· ∈ p₁)] (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ (h : p₁ → p₂), Function.Bijective h ∧ ∀ (a : p₁), G.Adj a (h a) := by
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun x ↦ G.neighborFinset x) |>.mp fun s ↦ by
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  have (x : V) (h : x ∈ p₁) : f x ∉ p₁ := h₁.disjoint |>.notMem_of_mem_right <|
    isBipartiteWith_neighborSet_subset h₁ h <| Set.mem_toFinset.mp <| hf₂ x
  have (x : V) (h : x ∈ p₂) : f x ∉ p₂ := h₁.disjoint |>.notMem_of_mem_left <|
    isBipartiteWith_neighborSet_subset h₁.symm h <| Set.mem_toFinset.mp <| hf₂ x
  have (x : V) : f x ∈ p₁ ∨ f x ∈ p₂ := by
    simp [union_eq_set_univ_of_forall_ncard_le h₁ h₂, p₁.mem_union (f x) p₂ |>.mp]
  let f' (x : p₁) : p₂ := ⟨f x, by grind⟩
  let g' (x : p₂) : p₁ := ⟨f x, by grind⟩
  refine Embedding.schroeder_bernstein' (f := f') (g := g') ?_ ?_ (fun x y ↦ G.Adj x y) ?_ ?_
  · exact Injective.of_comp (f := Subtype.val) <| hf₁.comp <| Subtype.val_injective
  · exact Injective.of_comp (f := Subtype.val) <| hf₁.comp <| Subtype.val_injective
  · exact fun v ↦ mem_neighborFinset _ _ _ |>.mp (hf₂ v)
  · exact fun v ↦ mem_neighborFinset _ _ _ |>.mp (hf₂ v) |>.symm

/-- This is the version of **Hall's marriage theorem** for bipartite graphs that finds a perfect
matching given that the neighborhood-condition holds globally. -/
theorem exists_IsPerfectMatching_of_forall_ncard_le [DecidablePred (· ∈ p₁)]
    (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : Subgraph G, M.IsPerfectMatching := by
  obtain ⟨b, hb₁, hb₂⟩ := exists_bijective_of_forall_ncard_le h₁ h₂
  use hall_subgraph (fun v ↦ (b v).1) (fun v hv ↦ h₁.disjoint |>.notMem_of_mem_right (b ⟨v, hv⟩).2)
    (fun v h ↦ hb₂ ⟨v, by assumption⟩)
  have : p₁ ∪ (Set.range (fun v ↦ (b v).1)) = Set.univ := by
    rw [Set.range_comp', hb₁.surjective.range_eq, Subtype.coe_image_univ]
    exact union_eq_set_univ_of_forall_ncard_le h₁ h₂
  refine ⟨fun v _ ↦ ?_, by simp [Subgraph.IsSpanning, this]⟩
  simp only [dite_else_false]
  split
  · exact existsUnique_eq'
  · obtain ⟨x, _⟩ := hb₁.existsUnique ⟨v, by grind⟩
    exact ⟨x, by grind⟩

end SimpleGraph
