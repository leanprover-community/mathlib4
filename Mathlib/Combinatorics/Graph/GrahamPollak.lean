/-
Copyright (c) 2026 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman, Aaron Hill
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!

# The Graham-Pollak theorem

-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V} {α : Type*} {a : α}

open Set

def IsCompleteWith {ι : Type} (G : SimpleGraph V) (parts : ι → Set V) : Prop :=
  ∀ i, ∀ v ∈ parts i, ∀ j, i ≠ j → ∀ u ∈ parts j, G.Adj v u

structure CompleteBipartite (G : SimpleGraph V) where
  left : Set V
  right : Set V
  bipartite : G.IsBipartiteWith left right
  complete : G.IsCompleteWith ![left, right]

namespace CompleteBipartite

variable {C : CompleteBipartite G}

lemma adj_of_mem_left_mem_right (hv : v ∈ C.left) (hu : u ∈ C.right) : G.Adj v u := by
  simpa using C.complete 0 v hv 1 (by decide) u hu

lemma adj_of_mem_right_mem_left (hv : v ∈ C.right) (hu : u ∈ C.left) : G.Adj v u :=
  adj_of_mem_left_mem_right hu hv |> G.adj_symm

lemma neighborSet_eq_of_mem_left (hv : v ∈ C.left) : G.neighborSet v = C.right := by
  grind [mem_neighborSet, adj_of_mem_left_mem_right,
         isBipartiteWith_neighborSet_subset C.bipartite hv]

lemma neighborSet_eq_of_mem_right (hv : v ∈ C.right) : G.neighborSet v = C.left := by
  grind [mem_neighborSet, isBipartiteWith_comm, IsBipartiteWith.mem_of_mem_adj,
         C.bipartite, adj_of_mem_right_mem_left]

section finite

variable [Fintype (G.neighborSet v)] [Fintype C.left] [Fintype C.right] [Fintype α]

lemma neighborFinset_eq_of_mem_left (hv : v ∈ C.left.toFinset) :
    G.neighborFinset v = C.right.toFinset := by
  grind [neighborFinset_def, neighborSet_eq_of_mem_left, toFinset_congr]

lemma neighborFinset_eq_of_mem_right (hv : v ∈ C.right.toFinset) :
    G.neighborFinset v = C.left.toFinset := by
  grind [neighborFinset_def, neighborSet_eq_of_mem_right, toFinset_congr]

lemma neighborFinset_eq_empty_of_notMem_union [DecidableEq V]
    (hv : v ∉ C.left.toFinset ∪ C.right.toFinset) : G.neighborFinset v = ∅ := by
  ext u
  simp only [mem_neighborFinset, Finset.notMem_empty, iff_false]
  intro h
  grind [C.bipartite.mem_of_adj <| G.mem_edgeSet.2 h]

end finite

end CompleteBipartite

section finite

variable [Fintype V] [Fintype α] {𝓁 : TopEdgeLabeling V α}

open Finset

/--
If `c` sums to 0 over `V` and over the left side of each complete bipartite subgraph
in a partition of `K_n`, then `∑ c_v^2 = 0`.
-/
private lemma aux
  (completeBipartiteOf : ∀ a, CompleteBipartite <| 𝓁.labelGraph a)
  [∀ a, Fintype (completeBipartiteOf a).left]
  (c : V → ℝ)
  (h_sum : ∑ v, c v = 0)
  (h_left : ∀ a, ∑ v ∈ (completeBipartiteOf a).left, c v = 0) :
    ∑ v, c v ^ 2 = 0 := by
  rcases subsingleton_or_nontrivial V
  · simp_rw [sq, sum_mul_self_eq_zero_iff]
    grind [Fintype.sum_subsingleton c]
  · classical
    have h_disjoint (u : V) :
        ((univ : Finset α) : Set α).PairwiseDisjoint (𝓁.labelGraph · |>.neighborFinset u) := by
      intro
      grind [Finset.disjoint_left, mem_neighborFinset, 𝓁.labelGraph_adj]
    have h_partition (u : V) :
        univ.erase u = (univ : Finset α).biUnion (𝓁.labelGraph · |>.neighborFinset u) := by
      ext v
      simp only [mem_erase, Finset.mem_univ, Finset.mem_biUnion, mem_neighborFinset]
      constructor
      · exact fun _ ↦ ⟨𝓁 ⟨s(u, v), by tauto⟩, by tauto⟩
      · grind only [TopEdgeLabeling.labelGraph_adj]
    have : ∑ v, c v ^ 2 = -∑ u, ∑ v ∈ univ.erase u, c u * c v := by simp [← mul_sum, sq, h_sum]
    rw [this,
        neg_eq_zero,
        sum_congr rfl fun u _ ↦ by rw [h_partition, sum_biUnion <| h_disjoint _],
        sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    let cbp := completeBipartiteOf a
    let sum_eq (S : Finset V) := ∑ x ∈ S, ∑ i ∈ 𝓁.labelGraph a |>.neighborFinset x, c x * c i = 0
    have h_L_sum : sum_eq cbp.left.toFinset := by
      dsimp [sum_eq]
      rw [sum_congr rfl fun _ hx ↦ by rw [cbp.neighborFinset_eq_of_mem_left hx, ← mul_sum],
          ← sum_mul, h_left a, zero_mul]
    have h_R_sum : sum_eq cbp.right.toFinset := by
      dsimp [sum_eq]
      rw [sum_congr rfl fun _ hx ↦ by rw [cbp.neighborFinset_eq_of_mem_right hx, ← mul_sum],
          h_left]
      simp only [mul_zero, sum_const_zero]
    rw [← sum_subset (subset_univ (cbp.left.toFinset ∪ cbp.right.toFinset)) <| fun _ _ hu ↦ by rw
      [cbp.neighborFinset_eq_empty_of_notMem_union hu, sum_empty],
        sum_union <| Finset.disjoint_left.mpr fun v hvL hvR ↦
          Set.disjoint_left.mp cbp.bipartite.disjoint
            (Set.mem_toFinset.mp hvL) (Set.mem_toFinset.mp hvR),
        h_L_sum,
        h_R_sum,
        add_zero]

open Fintype LinearMap in
open scoped Matrix in
/--
The Graham-Pollak theorem:

In a complete graph on `|V|` vertices, any edge labeling into complete bipartite subgraphs uses
at least `|V| - 1` distinct labels.
-/
theorem card_le_card_labels_add_one_of_CompleteBipartite
  (completeBipartiteOf : ∀ a, CompleteBipartite <| 𝓁.labelGraph a) :
    card V ≤ card α + 1 := by
  classical
  by_contra! h
  let M : Matrix (Fin 1 ⊕ α) V ℝ := Matrix.fromRows
    (Matrix.replicateCol V ![1])
    (Matrix.of fun m n ↦ (completeBipartiteOf m).left.indicator 1 n)
  obtain ⟨c, hc, hc_nezero⟩ : ∃ x ∈ ker M.toLin', x ≠ 0 := (ker _).ne_bot_iff.mp <| by
    apply ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, card_sum, card_unique]
    grind
  have (a : α) : ∑ v ∈ (completeBipartiteOf a).left, c v = 0 := by
    suffices ∑ x, ((completeBipartiteOf a).left.toFinset : Set _).indicator c x = 0 by
      rwa [sum_indicator_subset _ (by simp)] at this
    have : (M *ᵥ c) (.inr a) = 0 := by simp_all
    simp only [M, Matrix.mulVec, dotProduct, Set.indicator_apply] at this
    aesop
  have := aux completeBipartiteOf c
  simp_all [Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg, funext_iff, Matrix.mulVec, dotProduct]
  aesop

end finite

end SimpleGraph
