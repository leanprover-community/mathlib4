/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.MyGraph.Finite
import Mathlib.Combinatorics.MyGraph.Maps

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

namespace MyGraph

variable {V : Type*} (G : MyGraph V) (s t : V)

namespace Iso

variable {G} {W : Type*} {G' : MyGraph W} (f : G ≃g G')

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
def replaceVertex (h : t ∈ G.verts): MyGraph V where
  verts := G.verts
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  edge_vert := by
    intro v w
    split_ifs with h1 h2 h3
    · intro hf; exact hf.elim
    · intro _; exact (h1 ▸ h)
    · intro h; exact G.edge_vert h
    · intro h; exact G.edge_vert h
  symm v w := by dsimp only; split_ifs <;> simp [adj_comm]
  loopless := by
    intro v h'
    split_ifs at h'
    exact G.loopless _ h'


/-- There is never an `s-t` edge in `G.replaceVertex s t`. -/
lemma not_adj_replaceVertex_same (ht : t ∈ G.verts): ¬(G.replaceVertex s t ht).Adj s t :=
  by simp [replaceVertex]

@[simp] lemma replaceVertex_self (hs : s ∈ G.verts) : G.replaceVertex s s hs = G := by
  ext
  · rw [replaceVertex]
  · unfold replaceVertex; aesop (add simp or_iff_not_imp_left)

variable {t}

/-- Except possibly for `t`, the neighbours of `s` in `G.replaceVertex s t` are its neighbours in
`G`. -/
lemma adj_replaceVertex_iff_of_ne_left {w : V} (hw : w ≠ t) (ht : t ∈ G.verts) :
    (G.replaceVertex s t ht).Adj s w ↔ G.Adj s w := by simp [replaceVertex, hw]

/-- Except possibly for itself, the neighbours of `t` in `G.replaceVertex s t` are the neighbours of
`s` in `G`. -/
lemma adj_replaceVertex_iff_of_ne_right {w : V} (hw : w ≠ t) (ht : t ∈ G.verts):
    (G.replaceVertex s t ht).Adj t w ↔ G.Adj s w := by simp [replaceVertex, hw]

/-- Adjacency in `G.replaceVertex s t` which does not involve `t` is the same as that of `G`. -/
lemma adj_replaceVertex_iff_of_ne {v w : V} (hv : v ≠ t) (hw : w ≠ t) (ht : t ∈ G.verts):
    (G.replaceVertex s t ht).Adj v w ↔ G.Adj v w := by simp [replaceVertex, hv, hw]

variable {s}

theorem edgeSet_replaceVertex_of_not_adj (hn : ¬G.Adj s t) (ht : t ∈ G.verts) :
    (G.replaceVertex s t ht).edgeSet =
        G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s) := by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_diff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by aesop]

theorem edgeSet_replaceVertex_of_adj (ha : G.Adj s t) (ht : t ∈ G.verts) :
    (G.replaceVertex s t ht).edgeSet =
    (G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s)) \ {s(t, t)} := by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_diff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by aesop]

variable [Fintype V] [DecidableRel G.Adj]

instance (ht : t ∈ G.verts) : DecidableRel (G.replaceVertex s t ht).Adj := by
  unfold replaceVertex; infer_instance

theorem edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) (ht : t ∈ G.verts) :
  (G.replaceVertex s t ht).edgeFinset =
    G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (s(·, t)) := by
  simp only [incidenceFinset, neighborFinset, ← Set.toFinset_diff, ← Set.toFinset_image,
    ← Set.toFinset_union]
  exact Set.toFinset_congr (G.edgeSet_replaceVertex_of_not_adj hn ht)

theorem edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) (ht : t ∈ G.verts) :
    (G.replaceVertex s t ht).edgeFinset =
    (G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (s(·, t))) \ {s(t, t)} := by
  simp only [incidenceFinset, neighborFinset, ← Set.toFinset_diff, ← Set.toFinset_image,
    ← Set.toFinset_union, ← Set.toFinset_singleton]
  exact Set.toFinset_congr (G.edgeSet_replaceVertex_of_adj ha ht)

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

theorem card_edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) (ht : t ∈ G.verts) :
    #(G.replaceVertex s t ht).edgeFinset = #G.edgeFinset + G.degree s - G.degree t := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn,
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff inc,
    ← Nat.sub_add_comm <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

theorem card_edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) (ht : t ∈ G.verts) :
    #(G.replaceVertex s t ht).edgeFinset = #G.edgeFinset + G.degree s - G.degree t - 1 := by
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
def edge : MyGraph V := fromEdgeSet {s(s, t)}

lemma edge_adj (v w : V) : (edge s t).Adj v w ↔ (v = s ∧ w = t ∨ v = t ∧ w = s) ∧ v ≠ w := by
  rw [edge, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]

@[simp]
lemma edge_verts {s t : V} [DecidableEq V] :
    (edge s t).verts = if s = t then ∅ else {s, t} := by
  ext x
  rw [edge]
  aesop

lemma adj_edge {v w : V} : (edge s t).Adj v w ↔ s(s, t) = s(v, w) ∧ v ≠ w := by
  simp only [edge_adj, ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
    and_congr_left_iff]
  tauto

lemma edge_comm : edge s t = edge t s := by
  rw [edge, edge, Sym2.eq_swap]

variable [DecidableEq V] in
instance : DecidableRel (edge s t).Adj := fun _ _ ↦ by
  rw [edge_adj]; infer_instance

lemma edge_self_eq_bot  : edge s s = ⊥ := by
  classical
  ext x y
  · rw [edge_verts, if_pos rfl, bot_verts]
  · rw [edge_adj];
    simp only [or_self, ne_eq, not_bot_adj, iff_false, not_and, Decidable.not_not, and_imp]
    intro h1 h2
    exact (h2 ▸ h1)

@[simp]
lemma sup_edge_self : G ⊔ edge s s = G := by
  rw [edge_self_eq_bot, sup_of_le_left bot_le]

lemma lt_sup_edge (hne : s ≠ t) (hn : ¬ G.Adj s t) : G < G ⊔ edge s t :=
  left_lt_sup.2 fun h ↦ hn <| h.2 <| (edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩

variable {s t}

@[simp]
lemma edge_edgeSet_of_eq (h : s = t) : (edge s t).edgeSet = ∅ := by
  ext e;
  rw [edge, edgeSet_fromEdgeSet]
  simp only [h, Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and, not_not]
  rintro rfl
  simp

@[simp]
lemma edge_edgeSet_of_ne (h : s ≠ t) : (edge s t).edgeSet = {s(s, t)} := by
  rwa [edge, edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_singleton_left, Set.mem_setOf_eq,
    Sym2.isDiag_iff_proj_eq]

lemma sup_edge_of_adj (h : G.Adj s t) : G ⊔ edge s t = G := by
  classical
  ext x y
  · rw [sup_verts, edge_verts, if_neg h.ne]
    simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff]
    constructor
    · rintro (rfl | rfl | h')
      · exact G.edge_vert h
      · exact G.edge_vert h.symm
      · exact h'
    · intro h'
      exact Or.inr <| Or.inr h'
  · rw [sup_adj, or_iff_left_iff_imp, edge_adj]
    rintro ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ ,h'⟩
    · exact h
    · exact h.symm

lemma disjoint_edge_adj {u v : V} : Disjoint G.edgeSet (edge u v).edgeSet ↔ ¬G.Adj u v := by
  by_cases h : u = v <;> simp [h]

lemma sdiff_edge {u v : V} (h : ¬G.Adj u v) : G \ edge u v = G := by
  ext x y
  · simp
  · simp only [sdiff_adj, and_iff_left_iff_imp]
    intro h' h1
    rw [edge_adj] at h1
    cases h1.1 with
    | inl h1 => exact h (h1.1 ▸ (h1.2 ▸ h'))
    | inr h1 => exact h (h1.1 ▸ (h1.2 ▸ h'.symm))

/-- Need s,t in G.verts for actual subgraphs here -/
theorem edgeSet_sup_edge_le {H : MyGraph V} (hH : H ≤ G ⊔ edge s t)
    (h : ¬ H.Adj s t) : H.edgeSet ⊆ G.edgeSet := by
  intro e;
  cases e with
  | h v w =>
  simp_rw [mem_edgeSet]
  intro hvw
  have := hH.2 hvw
  simp only [sup_adj] at this
  by_cases hs : s(v, w) = s(s, t)
  · exact (h ((adj_congr_of_sym2 hs).mp hvw)).elim
  · rw [adj_edge] at this
    cases this with
    | inl h => exact h
    | inr h => exact (hs h.1.symm).elim

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

end MyGraph
