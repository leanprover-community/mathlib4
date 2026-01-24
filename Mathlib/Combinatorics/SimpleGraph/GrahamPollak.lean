/-
Copyright (c) 2026 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman, Aaron Hill
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!

# The Graham-Pollak theorem

-/

@[expose] public section

namespace SimpleGraph.completeGraph

variable {V α : Type*} [Fintype V] {G : SimpleGraph V} [Fintype α] {𝓁 : TopEdgeLabeling V α}

open Finset Fintype LinearMap in
open scoped Matrix in
/--
The Graham-Pollak theorem:

In a complete graph on `|V|` vertices, any edge labeling into complete bipartite subgraphs uses
at least `|V| - 1` distinct labels.
-/
theorem card_le_card_add_one_of_forall_IsCompleteBipartite
  (completeBipartiteOf : ∀ a, ∃ left, 𝓁.labelGraph a |>.IsCompleteBipartiteWith left) :
    card V ≤ card α + 1 := by
  classical
  rcases subsingleton_or_nontrivial V
  · grind [card_le_one_iff_subsingleton]
  · let M : Matrix (Fin 1 ⊕ α) V ℝ := Matrix.fromRows
      (Matrix.replicateCol V ![1])
      (Matrix.of fun m n ↦ (completeBipartiteOf m).choose.indicator 1 n)
    by_contra! h
    obtain ⟨c, hc, _⟩ : ∃ x ∈ ker M.toLin', x ≠ 0 := (ker _).exists_mem_ne_zero_of_ne_bot <| by
      apply ker_ne_bot_of_finrank_lt
      simp only [Module.finrank_fintype_fun_eq_card, card_sum, card_unique]
      grind
    have h_sum : ∑ v, c v = 0 := by
      have : (M *ᵥ c) (.inl 0) = 0 := by simp_all
      simp only [M, Matrix.mulVec, dotProduct] at this
      aesop
    have h_disjoint (u : V) :
        ((univ : Finset α) : Set α).PairwiseDisjoint (𝓁.labelGraph · |>.neighborFinset u) := by
      intro
      grind [Finset.disjoint_left, mem_neighborFinset, 𝓁.labelGraph_adj]
    have h_partition (u : V) :
        univ.erase u = (univ : Finset α).biUnion (𝓁.labelGraph · |>.neighborFinset u) := by
      ext v
      simp only [mem_erase, Finset.mem_univ, Finset.mem_biUnion, mem_neighborFinset]
      exact ⟨fun _ ↦ ⟨𝓁 ⟨s(u, v), by tauto⟩, by tauto⟩,
            by grind only [TopEdgeLabeling.labelGraph_adj]⟩
    have h_sq : ∑ v, c v ^ 2 = -∑ u, ∑ v ∈ univ.erase u, c u * c v :=
      by simp [← mul_sum, sq, h_sum]
    have h_zero : ∑ v, c v ^ 2 = 0 := by
      rw [h_sq,
          Finset.sum_congr rfl fun u _ ↦ by rw [h_partition, sum_biUnion <| h_disjoint _],
          neg_eq_zero,
          sum_comm]
      refine sum_eq_zero fun v _ ↦ ?_
      let cbp := completeBipartiteOf v
      have h_left : ∑ u ∈ (completeBipartiteOf v).choose, c u = 0 := by
        suffices ∑ x, ((completeBipartiteOf v).choose.toFinset : Set _).indicator c x = 0 by
          rwa [sum_indicator_subset _ (by simp)] at this
        have : (M *ᵥ c) (.inr v) = 0 := by simp_all
        simp only [M, Matrix.mulVec, dotProduct, Set.indicator_apply] at this
        aesop
      let sum_eq (S : Finset V) := ∑ x ∈ S, ∑ i ∈ 𝓁.labelGraph v |>.neighborFinset x, c x * c i = 0
      have h_L_sum : sum_eq cbp.choose.toFinset := by
        dsimp [sum_eq]
        rw [Finset.sum_congr rfl fun _ hv ↦ by
          rw [cbp.choose_spec.neighborFinset_eq_of_mem_left hv, ← mul_sum],
            ← sum_mul, h_left, zero_mul]
      have h_R_sum : sum_eq cbp.chooseᶜ.toFinset := by
        dsimp [sum_eq]
        rw [Finset.sum_congr rfl fun _ hx ↦ by
          rw [cbp.choose_spec.neighborFinset_eq_of_not_mem_left (by grind), ← mul_sum],
            h_left]
        simp only [mul_zero, sum_const_zero]
      rw [show univ = cbp.choose.toFinset ∪ cbp.chooseᶜ.toFinset by simp,
          sum_union <| Finset.disjoint_left.mpr fun v hvL hvR ↦
            Set.disjoint_left.mp cbp.choose_spec.bipartite.disjoint
              (Set.mem_toFinset.mp hvL) (Set.mem_toFinset.mp hvR),
          h_L_sum,
          h_R_sum,
          add_zero]
    simp only [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _), sq_eq_zero_iff] at h_zero
    bound

end SimpleGraph.completeGraph
