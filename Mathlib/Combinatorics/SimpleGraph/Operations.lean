/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Local graph operations

This file defines some single-graph operations that modify a finite number of vertices
and proves basic theorems about them. When the graph itself has a finite number of vertices
we also prove theorems about the number of edges in the modified graphs.

## Main definitions

* `G.replaceVertex s t` is `G` with `t` replaced by a copy of `s`,
  removing the `s-t` edge if present.
* `edge s t` is the graph with a single `s-t` edge. Adding this edge to a graph `G` is then
  `G ⊔ edge s t`.
-/


open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (s t : V)

namespace Iso

variable {G} {W : Type*} {G' : SimpleGraph W} (f : G ≃g G')

include f in
theorem card_edgeFinset_eq [Fintype G.edgeSet] [Fintype G'.edgeSet] :
    #G.edgeFinset = #G'.edgeFinset := by
  apply Finset.card_eq_of_equiv
  simp only [Set.mem_toFinset]
  exact f.mapEdgeSet

end Iso

section ReplaceVertex

variable [DecidableEq V]

/-- The graph formed by forgetting `t`'s neighbours and instead giving it those of `s`. The `s-t`
edge is removed if present. -/
def replaceVertex : SimpleGraph V where
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm v w := by dsimp only; split_ifs <;> simp [adj_comm]

/-- There is never an `s-t` edge in `G.replaceVertex s t`. -/
lemma not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t := by simp [replaceVertex]

@[simp] lemma replaceVertex_self : G.replaceVertex s s = G := by
  ext; unfold replaceVertex; aesop (add simp or_iff_not_imp_left)

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
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_diff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by aesop]

theorem edgeSet_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeSet =
    (G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s)) \ {s(t, t)} := by
  ext e; refine e.inductionOn ?_
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
    #(G.replaceVertex s t).edgeFinset = #G.edgeFinset + G.degree s - G.degree t := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn,
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff inc,
    ← Nat.sub_add_comm <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

theorem card_edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) :
    #(G.replaceVertex s t).edgeFinset = #G.edgeFinset + G.degree s - G.degree t - 1 := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_adj ha, card_sdiff (by simp [ha]),
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff inc,
    ← Nat.sub_add_comm <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

end ReplaceVertex

section AddEdge

/-- The graph with a single `s-t` edge. It is empty iff `s = t`. -/
def edge : SimpleGraph V := fromEdgeSet {s(s, t)}

lemma edge_adj (v w : V) : (edge s t).Adj v w ↔ (v = s ∧ w = t ∨ v = t ∧ w = s) ∧ v ≠ w := by
  rw [edge, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]

variable [DecidableEq V] in
instance : DecidableRel (edge s t).Adj := fun _ _ ↦ by
  rw [edge_adj]; infer_instance

lemma edge_self_eq_bot : edge s s = ⊥ := by
  ext; rw [edge_adj]; aesop

@[simp]
lemma sup_edge_self : G ⊔ edge s s = G := by
  rw [edge_self_eq_bot, sup_of_le_left bot_le]

variable {s t}

lemma edge_edgeSet_of_ne (h : s ≠ t) : (edge s t).edgeSet = {s(s, t)} := by
  rwa [edge, edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_singleton_left, Set.mem_setOf_eq,
    Sym2.isDiag_iff_proj_eq]

lemma sup_edge_of_adj (h : G.Adj s t) : G ⊔ edge s t = G := by
  rwa [sup_eq_left, ← edgeSet_subset_edgeSet, edge_edgeSet_of_ne h.ne, Set.singleton_subset_iff,
    mem_edgeSet]

variable [Fintype V] [DecidableRel G.Adj]

variable [DecidableEq V] in
instance : Fintype (edge s t).edgeSet := by rw [edge]; infer_instance

theorem edgeFinset_sup_edge [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s ≠ t) :
    (G ⊔ edge s t).edgeFinset = G.edgeFinset.cons s(s, t) (by simp_all) := by
  letI := Classical.decEq V
  rw [edgeFinset_sup, cons_eq_insert, insert_eq, union_comm]
  simp_rw [edgeFinset, edge_edgeSet_of_ne h]; rfl

theorem card_edgeFinset_sup_edge [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s ≠ t) :
    #(G ⊔ edge s t).edgeFinset = #G.edgeFinset + 1 := by
  rw [G.edgeFinset_sup_edge hn h, card_cons]

end AddEdge

section DeleteIncidenceSet

/-- Given a vertex `x`, remove the edges incident to `x` from the edge set. -/
abbrev deleteIncidenceSet (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (G.incidenceSet x)

lemma deleteIncidenceSet_adj {G : SimpleGraph V} {x v₁ v₂ : V} :
    (G.deleteIncidenceSet x).Adj v₁ v₂ ↔ G.Adj v₁ v₂ ∧ v₁ ≠ x ∧ v₂ ≠ x := by
  rw [deleteEdges_adj, mk'_mem_incidenceSet_iff]
  tauto

lemma deleteIncidenceSet_le (G : SimpleGraph V) (x : V) : G.deleteIncidenceSet x ≤ G := by
  intro v₁ v₂
  rw [deleteIncidenceSet_adj]
  tauto

lemma edgeSet_fromEdgeSet_incidenceSet (G : SimpleGraph V) (x : V) :
    (fromEdgeSet (G.incidenceSet x)).edgeSet = G.incidenceSet x := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, ←Set.subset_compl_iff_disjoint_right, Set.compl_setOf]
  exact (incidenceSet_subset G x).trans G.edgeSet_subset_setOf_not_isDiag

/-- The edge set of `G.deleteIncidenceSet x` is the edge set of `G` set difference the incidence
set of the vertex `x`. -/
theorem edgeSet_deleteIncidenceSet (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).edgeSet = G.edgeSet \ (G.incidenceSet x) := by
  simp_rw [deleteEdges, edgeSet_sdiff, edgeSet_fromEdgeSet_incidenceSet]

/-- The support of `G.deleteIncidenceSet x` is a subset of the support of `G` set difference the
singleton set `{x}`. -/
theorem deleteIncidenceSet_support_subset (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).support ⊆ G.support \ {x} := by
  intro v
  simp_rw [mem_support, deleteIncidenceSet_adj]
  tauto

/-- If the vertex `x` is not in the set `s`, then the induced subgraph in `G.deleteIncidenceSet x`
by `s` is equal to the induced subgraph in `G` by `s`. -/
theorem deleteIncidenceSet_induce_of_not_mem (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s) :
    (G.deleteIncidenceSet x).induce s = G.induce s := by
  ext v₁ v₂
  simp_rw [comap_adj, Function.Embedding.coe_subtype, deleteIncidenceSet_adj, and_iff_left_iff_imp]
  intro hadj
  exact ⟨v₁.prop.ne_of_not_mem h, v₂.prop.ne_of_not_mem h⟩

variable [Fintype V]

/-- If the support of the simple graph `G` is a subset of the set `s`, then the induced subgraph of
`s` has the same number of edges as `G`. -/
theorem card_edgeFinset_induce_of_support_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    {s : Set V} [DecidablePred (· ∈ s)] (h : G.support ⊆ s) :
    #(G.induce s).edgeFinset = #G.edgeFinset := by
  apply Finset.card_bij (fun e _ ↦ e.map (↑))
  · apply Sym2.ind; simp
  · apply Sym2.ind
    intro _ _ _
    apply Sym2.ind
    simp [Subtype.ext_iff]
  · apply Sym2.ind
    intro v₁ v₂ hadj
    rw [mem_edgeFinset, mem_edgeSet] at hadj
    have hv₁ : v₁ ∈ G.support := by
      rw [mem_support]
      exact ⟨v₂, hadj⟩
    have hv₂ : v₂ ∈ G.support := by
      rw [mem_support]
      exact ⟨v₁, hadj.symm⟩
    use s(⟨v₁, h hv₁⟩, ⟨v₂, h hv₂⟩)
    simp [hadj]

variable [DecidableEq V]

/-- Deleting the incidence set of the vertex `x` retains the same number of edges as in the induced
subgraph of the vertices `{x}ᶜ`. -/
theorem card_edgeFinset_induce_compl_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset := by
  trans ((G.deleteIncidenceSet x).induce {x}ᶜ).edgeFinset.card
  · have h_not_mem : x ∉ ({x}ᶜ : Set V) := by
      rw [Set.not_mem_compl_iff]
      exact Set.mem_singleton x
    simp_rw [Set.toFinset_card, G.deleteIncidenceSet_induce_of_not_mem h_not_mem]
  · apply card_edgeFinset_induce_of_support_subset
    trans G.support \ {x}
    · exact deleteIncidenceSet_support_subset G x
    · rw [Set.compl_eq_univ_diff]
      apply Set.diff_subset_diff_left
      exact Set.subset_univ G.support

/-- The finite edge set of `G.deleteIncidenceSet x` is the finite edge set of the simple graph `G`
set difference the finite incidence set of the vertex `x`. -/
theorem edgeFinset_deleteIncidenceSet_eq_sdiff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset \ (G.incidenceFinset x) := by
  rw [←Set.toFinset_diff, Set.toFinset_inj]
  exact G.edgeSet_deleteIncidenceSet x

lemma incidenceFinset_subset (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    G.incidenceFinset x ⊆ G.edgeFinset := by
  rw [Set.toFinset_subset_toFinset]
  exact G.incidenceSet_subset x

/-- Deleting the incident set of the vertex `x` deletes exactly `G.degree x` edges from the edge
set of the simple graph `G`. -/
theorem card_edgeFinset_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset-G.degree x := by
  simp_rw [←card_incidenceFinset_eq_degree, ←Finset.card_sdiff (G.incidenceFinset_subset x),
    edgeFinset_deleteIncidenceSet_eq_sdiff]

/-- Deleting the incident set of the vertex `x` is equivalent to filtering the edges of the simple
graph `G` that do not contain `x`. -/
theorem edgeFinset_deleteIncidenceSet_eq_filter (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset.filter (x ∉ ·) := by
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff, sdiff_eq_filter]
  apply Finset.filter_congr
  intro e he
  rw [Set.mem_toFinset, incidenceSet, Set.mem_setOf_eq, not_and, Classical.imp_iff_right_iff]
  left; rwa [mem_edgeFinset] at he

/-- The support of `G.deleteIncidenceSet x` is at most `1` less than the support of the simple
graph `G`. -/
theorem card_support_deleteIncidenceSet
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} (hx : x ∈ G.support) :
    Fintype.card (G.deleteIncidenceSet x).support ≤ Fintype.card G.support - 1 := by
  rw [←Set.singleton_subset_iff, ←Set.toFinset_subset_toFinset] at hx
  simp_rw [←Set.card_singleton x, ←Set.toFinset_card, ←Finset.card_sdiff hx, ←Set.toFinset_diff]
  apply Finset.card_le_card
  rw [Set.toFinset_subset_toFinset]
  exact G.deleteIncidenceSet_support_subset x

end DeleteIncidenceSet

end SimpleGraph
