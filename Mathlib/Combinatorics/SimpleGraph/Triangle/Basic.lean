/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Positivity.Finset

#align_import combinatorics.simple_graph.triangle.basic from "leanprover-community/mathlib"@"3365b20c2ffa7c35e47e5209b89ba9abdddf3ffe"

/-!
# Triangles in graphs

A *triangle* in a simple graph is a `3`-clique, namely a set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `SimpleGraph.FarFromTriangleFree`: Predicate for a graph such that one must remove a lot of edges
  from it for it to become triangle-free. This is the crux of the Triangle Removal Lemma.

## TODO

* Generalise `farFromTriangleFree` to other graphs, to state and prove the Graph Removal Lemma.
-/


open Finset Fintype Nat

namespace SimpleGraph

variable {α 𝕜 : Type*} [DecidableEq α] [Fintype α] [LinearOrderedField 𝕜] (G H : SimpleGraph α)
  [DecidableRel G.Adj] [DecidableRel H.Adj] (ε δ : 𝕜) {n : ℕ} {s : Finset α}

/-- A simple graph is *`ε`-far from triangle-free* if one must remove at least
`ε * (card α) ^ 2` edges to make it triangle-free. -/
def FarFromTriangleFree : Prop := G.DeleteFar (fun H ↦ H.CliqueFree 3) <| ε * (card α ^ 2 : ℕ)
#align simple_graph.far_from_triangle_free SimpleGraph.FarFromTriangleFree

variable {G H ε δ}

theorem farFromTriangleFree_iff :
    G.FarFromTriangleFree ε ↔ ∀ ⦃H : SimpleGraph α⦄, [DecidableRel H.Adj] → H ≤ G → H.CliqueFree 3 →
      ε * (card α ^ 2 : ℕ) ≤ G.edgeFinset.card - H.edgeFinset.card := deleteFar_iff
#align simple_graph.far_from_triangle_free_iff SimpleGraph.farFromTriangleFree_iff

alias ⟨farFromTriangleFree.le_card_sub_card, _⟩ := farFromTriangleFree_iff
#align simple_graph.far_from_triangle_free.le_card_sub_card SimpleGraph.farFromTriangleFree.le_card_sub_card

nonrec theorem FarFromTriangleFree.mono (hε : G.FarFromTriangleFree ε) (h : δ ≤ ε) :
    G.FarFromTriangleFree δ := hε.mono <| by gcongr
#align simple_graph.far_from_triangle_free.mono SimpleGraph.FarFromTriangleFree.mono

theorem FarFromTriangleFree.cliqueFinset_nonempty' (hH : H ≤ G) (hG : G.FarFromTriangleFree ε)
    (hcard : (G.edgeFinset.card - H.edgeFinset.card : 𝕜) < ε * (card α ^ 2 : ℕ)) :
    (H.cliqueFinset 3).Nonempty :=
  nonempty_of_ne_empty <|
    cliqueFinset_eq_empty_iff.not.2 fun hH' => (hG.le_card_sub_card hH hH').not_lt hcard
#align simple_graph.far_from_triangle_free.clique_finset_nonempty' SimpleGraph.FarFromTriangleFree.cliqueFinset_nonempty'

variable [Nonempty α]

lemma FarFromTriangleFree.lt_half (hG : G.FarFromTriangleFree ε) : ε < 2⁻¹ := by
  by_contra! hε
  refine lt_irrefl (ε * card α ^ 2) ?_
  have hε₀ : 0 < ε := hε.trans_lt' (by norm_num)
  rw [inv_pos_le_iff_one_le_mul (zero_lt_two' 𝕜)] at hε
  calc
    _ ≤ (G.edgeFinset.card : 𝕜) := by
      simpa using hG.le_card_sub_card bot_le (cliqueFree_bot (le_succ _))
    _ ≤ ε * 2 * (edgeFinset G).card := le_mul_of_one_le_left (by positivity) (by assumption)
    _ < ε * card α ^ 2 := ?_
  rw [mul_assoc, mul_lt_mul_left hε₀]
  norm_cast
  calc
    _ ≤ 2 * (⊤ : SimpleGraph α).edgeFinset.card := by gcongr; exact le_top
    _ < card α ^ 2 := ?_
  rw [edgeFinset_top, filter_not, card_sdiff (subset_univ _), card_univ, Sym2.card,]
  simp_rw [choose_two_right, Nat.add_sub_cancel, Nat.mul_comm _ (card α),
    Sym2.isDiag_iff_mem_range_diag, univ_filter_mem_range, mul_tsub,
    Nat.mul_div_cancel' (card α).even_mul_succ_self.two_dvd]
  rw [card_image_of_injective _ Sym2.diag_injective, card_univ, mul_add_one (α := ℕ), two_mul, sq,
    add_tsub_add_eq_tsub_right]
  apply tsub_lt_self <;> positivity

lemma FarFromTriangleFree.lt_one (hG : G.FarFromTriangleFree ε) : ε < 1 :=
  hG.lt_half.trans $ inv_lt_one one_lt_two

theorem FarFromTriangleFree.nonpos (h₀ : G.FarFromTriangleFree ε) (h₁ : G.CliqueFree 3) :
    ε ≤ 0 := by
  have := h₀ (empty_subset _)
  rw [coe_empty, Finset.card_empty, cast_zero, deleteEdges_empty_eq] at this
  exact nonpos_of_mul_nonpos_left (this h₁) (cast_pos.2 <| sq_pos_of_pos Fintype.card_pos)
#align simple_graph.far_from_triangle_free.nonpos SimpleGraph.FarFromTriangleFree.nonpos

theorem CliqueFree.not_farFromTriangleFree (hG : G.CliqueFree 3) (hε : 0 < ε) :
    ¬G.FarFromTriangleFree ε := fun h => (h.nonpos hG).not_lt hε
#align simple_graph.clique_free.not_far_from_triangle_free SimpleGraph.CliqueFree.not_farFromTriangleFree

theorem FarFromTriangleFree.not_cliqueFree (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) :
    ¬G.CliqueFree 3 := fun h => (hG.nonpos h).not_lt hε
#align simple_graph.far_from_triangle_free.not_clique_free SimpleGraph.FarFromTriangleFree.not_cliqueFree

theorem FarFromTriangleFree.cliqueFinset_nonempty (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) :
    (G.cliqueFinset 3).Nonempty :=
  nonempty_of_ne_empty <| cliqueFinset_eq_empty_iff.not.2 <| hG.not_cliqueFree hε
#align simple_graph.far_from_triangle_free.clique_finset_nonempty SimpleGraph.FarFromTriangleFree.cliqueFinset_nonempty

end SimpleGraph
