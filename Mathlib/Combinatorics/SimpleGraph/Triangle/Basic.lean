/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.GCongr

#align_import combinatorics.simple_graph.triangle.basic from "leanprover-community/mathlib"@"cd7f0626a0b04be1dda223a26123313514a55fb4"

/-!
# Triangles in graphs

A *triangle* in a simple graph is a `3`-clique, namely a set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `SimpleGraph.farFromTriangleFree`: Predicate for a graph to have enough triangles that, to
  remove all of them, one must one must remove a lot of edges. This is the crux of the Triangle
  Removal lemma.

## TODO

* Generalise `farFromTriangleFree` to other graphs, to state and prove the Graph Removal Lemma.
* Find a better name for `farFromTriangleFree`. Added 4/26/2022. Remove this TODO if it gets old.
-/


open Finset Fintype Nat

open Classical

namespace SimpleGraph

variable {α 𝕜 : Type*} [Fintype α] [LinearOrderedField 𝕜] {G H : SimpleGraph α} {ε δ : 𝕜} {n : ℕ}
  {s : Finset α}

/-- A simple graph is *`ε`-triangle-free far* if one must remove at least `ε * (card α)^2` edges to
make it triangle-free. -/
def FarFromTriangleFree (G : SimpleGraph α) (ε : 𝕜) : Prop :=
  (G.DeleteFar fun H => H.CliqueFree 3) <| ε * (card α ^ 2 : ℕ)
#align simple_graph.far_from_triangle_free SimpleGraph.FarFromTriangleFree

theorem farFromTriangleFree_iff : G.FarFromTriangleFree ε ↔ ∀ ⦃H⦄, H ≤ G → H.CliqueFree 3 →
  ε * (card α ^ 2 : ℕ) ≤ G.edgeFinset.card - H.edgeFinset.card := deleteFar_iff
#align simple_graph.far_from_triangle_free_iff SimpleGraph.farFromTriangleFree_iff

alias farFromTriangleFree_iff ↔ farFromTriangleFree.le_card_sub_card _
#align simple_graph.far_from_triangle_free.le_card_sub_card SimpleGraph.farFromTriangleFree.le_card_sub_card

theorem farFromTriangleFree.mono (hε : G.FarFromTriangleFree ε) (h : δ ≤ ε) :
    G.FarFromTriangleFree δ := hε.mono <| by gcongr
#align simple_graph.far_from_triangle_free.mono SimpleGraph.farFromTriangleFree.mono

theorem FarFromTriangleFree.cliqueFinset_nonempty' (hH : H ≤ G) (hG : G.FarFromTriangleFree ε)
    (hcard : (G.edgeFinset.card - H.edgeFinset.card : 𝕜) < ε * (card α ^ 2 : ℕ)) :
    (H.cliqueFinset 3).Nonempty :=
  nonempty_of_ne_empty <|
    H.cliqueFinset_eq_empty_iff.not.2 fun hH' => (hG.le_card_sub_card hH hH').not_lt hcard
#align simple_graph.far_from_triangle_free.clique_finset_nonempty' SimpleGraph.FarFromTriangleFree.cliqueFinset_nonempty'

variable [Nonempty α]

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
  nonempty_of_ne_empty <| G.cliqueFinset_eq_empty_iff.not.2 <| hG.not_cliqueFree hε
#align simple_graph.far_from_triangle_free.clique_finset_nonempty SimpleGraph.FarFromTriangleFree.cliqueFinset_nonempty

end SimpleGraph
