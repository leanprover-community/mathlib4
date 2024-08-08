/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Order.Partition.Finpartition

/-!
# Dividing the edges of a graph by a vertex finpartition

Consider a finpartition `P` of the vertices of a finite graph. `P` induces a coarser graph,
whose "supervertices" are `P.parts` and whose "superedges" contain all regular edges whose vertices
lie in the relevant parts.

Then taking the union over superedges of the contained edges gives back `G.edgeFinset`.
This file proves the fact and specialises it to the case when `P` has two parts, specified by one
of the parts. This specialisation is intended for proving Turán's theorem
(`Mathlib.Combinatorics.SimpleGraph.Turan`).

## Main statements

* `G.interEdges se`: given the superedge `se : Sym2 P.parts`, returns the finset of all edges of `G`
  under said superedge.
* `SimpleGraph.card_edgeFinset_eq_sum_interEdges_card`: the superedges partition the edges of `G`.
* `SimpleGraph.card_edgeFinset_bipartition`: special case of the above theorem for `P` comprising
  two parts.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {P : Finpartition (univ : Finset V)}

/-- The finset of edges whose endpoints lie in the parts of the endpoint of the given superedge. -/
def interEdges (se : Sym2 (Finset V)) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e ↦ e.map P.part = se.map (↑))

lemma interEdges_self (p : P.parts) :
    G.interEdges s(p, p) =
      (G.induce p).edgeFinset.map ⟨_, Sym2.map.injective Subtype.val_injective⟩ := by
  ext e
  obtain ⟨p, mp⟩ := p
  refine e.inductionOn fun x y ↦ ?_
  simp_rw [interEdges, Sym2.map_pair_eq, mem_filter, mem_map, Sym2.map_pair_eq, Sym2.eq_iff,
    or_self, mem_edgeFinset, mem_edgeSet, Function.Embedding.coeFn_mk]
  constructor <;> intro h
  · have mx : x ∈ p := h.2.1 ▸ P.mem_part (mem_univ x)
    have my : y ∈ p := h.2.2 ▸ P.mem_part (mem_univ y)
    use s(⟨x, mx⟩, ⟨y, my⟩)
    simp [Function.Embedding.subtype, h.1]
  · rw [Sym2.exists] at h
    obtain ⟨⟨x, mx⟩, ⟨y, my⟩, f, q⟩ := h
    rw [mem_edgeSet, comap_adj, Function.Embedding.subtype, Function.Embedding.coeFn_mk] at f
    rw [Sym2.map_pair_eq, Sym2.eq_iff] at q
    rcases q with ⟨qx, qy⟩ | ⟨qx, qy⟩ <;> (subst qx qy; refine ⟨by simpa only [adj_comm], ?_, ?_⟩)
    all_goals exact P.part_eq_of_mem mp ‹_›

lemma interEdges_eq_biUnion (p q : P.parts) :
    G.interEdges s(p, q) = q.1.biUnion fun b ↦ (p.1.filter (G.Adj · b)).map
      ⟨(s(b, ·)), fun _ _ c ↦ Sym2.congr_right.mp c⟩ := by
  ext e
  refine e.inductionOn fun a b ↦ ?_
  simp only [interEdges, Sym2.map_pair_eq, mem_filter, Set.mem_toFinset, mem_edgeSet, Sym2.eq_iff,
    mem_biUnion, mem_map, Function.Embedding.coeFn_mk]
  refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
  · obtain ⟨adj, ⟨ca, cb⟩ | ⟨ca, cb⟩⟩ := j
    · use b, cb ▸ P.mem_part (mem_univ b), a
      have := ca ▸ P.mem_part (mem_univ a)
      tauto
    · use a, ca ▸ P.mem_part (mem_univ a), b
      have := cb ▸ P.mem_part (mem_univ b)
      tauto
  · obtain ⟨x, hx, y, ⟨hy, adj⟩, ⟨cx, cy⟩ | ⟨cx, cy⟩⟩ := j <;>
      (rw [cx] at adj hx; rw [cy] at adj hy)
    · exact ⟨adj.symm, Or.inr ⟨P.part_eq_of_mem q.2 hx, P.part_eq_of_mem p.2 hy⟩⟩
    · exact ⟨adj, Or.inl ⟨P.part_eq_of_mem p.2 hy, P.part_eq_of_mem q.2 hx⟩⟩

lemma card_interEdges_eq_sum_of_ne {p q : P.parts} (h : p ≠ q) :
    (G.interEdges s(p, q)).card = ∑ b in q.1, (p.1.filter (G.Adj · b)).card := by
  rw [interEdges_eq_biUnion, card_biUnion]
  · simp
  · simp_rw [disjoint_iff_ne, mem_map, mem_filter, forall_exists_index, and_imp,
      Function.Embedding.coeFn_mk]
    intro _ m₁ _ _ l _ _ _ _ e₁ _ _ m₂ _ e₂; subst e₁ e₂
    simp_rw [Ne, Sym2.eq_iff, l, false_and, false_or, not_and]
    intro z; subst z; have := P.eq_of_mem_parts q.2 p.2 m₁ m₂
    aesop

theorem pairwiseDisjoint_interEdges :
    (P.parts.sym2 : Set (Sym2 P.parts)).PairwiseDisjoint G.interEdges := by
  rintro x - y - hn
  contrapose! hn
  rw [not_disjoint_iff] at hn
  obtain ⟨e, mx, my⟩ := hn
  rw [interEdges, mem_filter] at mx my
  exact Sym2.map.injective Subtype.val_injective (mx.2 ▸ my.2)

theorem disjiUnion_interEdges :
    (univ : Finset (Sym2 P.parts)).disjiUnion G.interEdges
      (by simp [pairwiseDisjoint_interEdges]) = G.edgeFinset := by
  ext e
  refine e.inductionOn fun x y ↦ ?_
  simp_rw [disjiUnion_eq_biUnion, mem_biUnion, mem_univ, interEdges, mem_filter, Set.mem_toFinset,
    mem_edgeSet, Sym2.map_pair_eq, true_and, exists_and_left, Sym2.exists, Sym2.map_pair_eq,
    Sym2.eq_iff, Subtype.exists, exists_prop, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨P.part x, P.part_mem (mem_univ x), P.part y, P.part_mem (mem_univ y), by tauto⟩

theorem card_edgeFinset_eq_sum_interEdges_card :
    G.edgeFinset.card = ∑ se : Sym2 P.parts, (G.interEdges se).card := by
  rw [← disjiUnion_interEdges, card_disjiUnion]

variable {K : Finset V}

theorem card_edgeFinset_bipartition :
    G.edgeFinset.card = (G.induce K).edgeFinset.card +
      ∑ b in Kᶜ, (K.filter (G.Adj · b)).card + (G.induce Kᶜ).edgeFinset.card := by
  have t1 : (G.induce (∅ : Finset V).toSetᶜ).edgeFinset.card = G.edgeFinset.card := by
    convert G.induceUnivIso.card_edgeFinset_eq <;> simp
  have t2 : (G.induce (univ : Finset V)).edgeFinset.card = G.edgeFinset.card := by
    convert G.induceUnivIso.card_edgeFinset_eq <;> simp
  have t3 : (G.induce (univ : Finset V).toSetᶜ).edgeFinset.card = 0 := by
    rw [card_eq_zero, Set.toFinset_eq_empty, edgeSet_eq_empty]
    ext a b
    obtain ⟨_, hx⟩ := a
    simp at hx
  have t4 : (induce (↑Kᶜ) G).edgeFinset.card = (induce (↑K)ᶜ G).edgeFinset.card := by
    apply Iso.card_edgeFinset_eq
    rw [← coe_compl]
  by_cases h1 : K = ∅
  · subst h1; simp [t1]
  by_cases h2 : K = univ
  · subst h2; rw [compl_univ, sum_empty, add_zero, t2, t3, add_zero]
  let P2 := Finpartition.properBipartition h1 h2
  simp_rw [G.card_edgeFinset_eq_sum_interEdges_card (P := P2), P2, Finpartition.properBipartition,
    Sym2.univ_pair]
  have nc : K ≠ Kᶜ := by
    let x := (nonempty_iff_ne_empty.mpr h1).choose
    haveI : Nontrivial (Finset V) := ⟨{x}, ∅, singleton_ne_empty x⟩
    exact ne_compl_self
  rw [sum_insert (by simp [nc]), sum_insert (by simp [nc]), sum_singleton,
    interEdges_self, interEdges_self, card_map, card_map, add_assoc, t4,
    G.card_interEdges_eq_sum_of_ne (by simp [nc])]

end SimpleGraph
