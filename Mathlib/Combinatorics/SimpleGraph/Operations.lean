/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Local graph operations

This file defines some single-graph operations that modify a finite number of vertices
and proves basic theorems about them. When the graph itself has a finite number of vertices
we also prove theorems about the number of edges in the modified graphs.

## Main definitions

* `G.replaceVertex s t` is `G` with `t` replaced by a copy of `s`,
  removing the `s-t` edge if present.
* `G.addEdge s t` is `G` with the `s-t` edge added, if that is a valid edge.
-/


open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s t : V)

section ReplaceVertex

/-- The graph formed by forgetting `t`'s neighbours and instead giving it those of `s`. The `s-t`
edge is removed if present. -/
def replaceVertex : SimpleGraph V where
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm v w := by dsimp only; split_ifs <;> simp [adj_comm]

/-- There is never an `s-t` edge in `G.replaceVertex s t`. -/
lemma not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t := by simp [replaceVertex]

@[simp]
lemma replaceVertex_self : G.replaceVertex s s = G := by ext; unfold replaceVertex; aesop

variable {t}

/-- Except possibly for `t`, the neighbours of `s` in `G.replaceVertex s t` are its neighbours in
`G`. -/
lemma adj_replaceVertex_iff_of_ne_left {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj s w ↔ G.Adj s w := by simp [replaceVertex, hw]

/-- Except possibly for itself, the neighbours of `t` in `G.replaceVertex s t` are the neighbours of
`s` in `G`. -/
lemma adj_replaceVertex_iff_of_ne_right {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj t w ↔ G.Adj s w := by simp [replaceVertex, hw]

/-- Adjacency in `G.replaceVertex s t` which does not involve `t` is the same as that of `G`. -/
lemma adj_replaceVertex_iff_of_ne {v w : V} (hv : v ≠ t) (hw : w ≠ t) :
    (G.replaceVertex s t).Adj v w ↔ G.Adj v w := by simp [replaceVertex, hv, hw]

variable {s}

theorem edgeSet_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeSet =
    G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s) := by
  ext e; refine' e.inductionOn _
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_diff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by aesop]

theorem edgeSet_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeSet =
    (G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s)) \ {s(t, t)} := by
  ext e; refine' e.inductionOn _
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_diff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by aesop]

variable [Fintype V] [DecidableRel G.Adj]

instance : DecidableRel (G.replaceVertex s t).Adj := by unfold replaceVertex; infer_instance

theorem edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (s(·, t)) := by
  simp only [incidenceFinset, neighborFinset, ← Set.toFinset_diff, ← Set.toFinset_image,
    ← Set.toFinset_union]
  exact Set.toFinset_congr (G.edgeSet_replaceVertex_of_not_adj hn)

theorem edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    (G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (s(·, t))) \ {s(t, t)} := by
  simp only [incidenceFinset, neighborFinset, ← Set.toFinset_diff, ← Set.toFinset_image,
    ← Set.toFinset_union, ← Set.toFinset_singleton]
  exact Set.toFinset_congr (G.edgeSet_replaceVertex_of_adj ha)

lemma disjoint_sdiff_neighborFinset_image :
    Disjoint (G.edgeFinset \ G.incidenceFinset t) ((G.neighborFinset s).image (s(·, t))) := by
  rw [disjoint_iff_ne]
  intro e he
  have : t ∉ e := by
    rw [mem_sdiff, mem_incidenceFinset] at he
    obtain ⟨_, h⟩ := he
    contrapose! h
    simp_all [incidenceSet]
  aesop

theorem card_edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) :
    (G.replaceVertex s t).edgeFinset.card = G.edgeFinset.card + G.degree s - G.degree t := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn,
    card_disjoint_union G.disjoint_sdiff_neighborFinset_image, card_sdiff inc,
    tsub_add_eq_add_tsub <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

theorem card_edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) :
    (G.replaceVertex s t).edgeFinset.card = G.edgeFinset.card + G.degree s - G.degree t - 1 := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_adj ha, card_sdiff (by simp [ha]),
    card_disjoint_union G.disjoint_sdiff_neighborFinset_image, card_sdiff inc,
    tsub_add_eq_add_tsub <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

end ReplaceVertex

section AddEdge

/-- Given a vertex pair, add the corresponding edge to the graph's edge set if not present. -/
def addEdge : SimpleGraph V where
  Adj v w := G.Adj v w ∨ s ≠ t ∧ (s = v ∧ t = w ∨ s = w ∧ t = v)
  symm v w := by simp_rw [adj_comm]; (conv_lhs => arg 2; arg 2; rw [or_comm]); exact id

@[simp]
lemma addEdge_self : G.addEdge s s = G := by ext; simp [addEdge]

variable {s t}

lemma addEdge_of_adj (h : G.Adj s t) : G.addEdge s t = G := by
  ext
  simp only [addEdge, ne_eq, G.ne_of_adj h, not_false_eq_true, true_and, or_iff_left_iff_imp]
  rintro (_ | _) <;> simp_all [adj_comm]

variable [Fintype V] [DecidableRel G.Adj]

instance : DecidableRel (G.addEdge s t).Adj := by unfold addEdge; infer_instance

theorem edgeFinset_addEdge (hn : ¬G.Adj s t) (h : s ≠ t) :
    (G.addEdge s t).edgeFinset = G.edgeFinset.cons s(s, t) (by simp_all) := by
  ext e; refine' e.inductionOn _; unfold addEdge; aesop

theorem card_edgeFinset_addEdge (hn : ¬G.Adj s t) (h : s ≠ t) :
    (G.addEdge s t).edgeFinset.card = G.edgeFinset.card + 1 := by
  rw [G.edgeFinset_addEdge hn h, card_cons]

end AddEdge
