/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Connectivity

#align_import combinatorics.simple_graph.trails from "leanprover-community/mathlib"@"edaaaa4a5774e6623e0ddd919b2f2db49c65add4"

/-!

# Trails and Eulerian trails

This module contains additional theory about trails, including Eulerian trails (also known
as Eulerian circuits).

## Main definitions

* `SimpleGraph.Walk.IsEulerian` is the predicate that a trail is an Eulerian trail.
* `SimpleGraph.Walk.IsTrail.even_countP_edges_iff` gives a condition on the number of edges
  in a trail that can be incident to a given vertex.
* `SimpleGraph.Walk.IsEulerian.even_degree_iff` gives a condition on the degrees of vertices
  when there exists an Eulerian trail.
* `SimpleGraph.Walk.IsEulerian.card_odd_degree` gives the possible numbers of odd-degree
  vertices when there exists an Eulerian trail.

## Todo

* Prove that there exists an Eulerian trail when the conclusion to
  `SimpleGraph.Walk.IsEulerian.card_odd_degree` holds.

## Tags

Eulerian trails

-/


namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace Walk

/-- The edges of a trail as a finset, since each edge in a trail appears exactly once. -/
abbrev IsTrail.edgesFinset {u v : V} {p : G.Walk u v} (h : p.IsTrail) : Finset (Sym2 V) :=
  ⟨p.edges, h.edges_nodup⟩
#align simple_graph.walk.is_trail.edges_finset SimpleGraph.Walk.IsTrail.edgesFinset

variable [DecidableEq V]

theorem IsTrail.even_countP_edges_iff {u v : V} {p : G.Walk u v} (ht : p.IsTrail) (x : V) :
    Even (p.edges.countP fun e => x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  induction' p with u u v w huv p ih
  · simp
  · rw [cons_isTrail_iff] at ht
    specialize ih ht.1
    simp only [List.countP_cons, Ne, edges_cons, Sym2.mem_iff]
    split_ifs with h
    · rw [decide_eq_true_eq] at h
      obtain (rfl | rfl) := h
      · rw [Nat.even_add_one, ih]
        simp only [huv.ne, imp_false, Ne, not_false_iff, true_and_iff, not_forall,
          Classical.not_not, exists_prop, eq_self_iff_true, not_true, false_and_iff,
          and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless _ huv
      · rw [Nat.even_add_one, ih, ← not_iff_not]
        simp only [huv.ne.symm, Ne, eq_self_iff_true, not_true, false_and_iff, not_forall,
          not_false_iff, exists_prop, and_true_iff, Classical.not_not, true_and_iff, iff_and_self]
        rintro rfl
        exact huv.ne
    · rw [decide_eq_true_eq, not_or] at h
      simp only [h.1, h.2, not_false_iff, true_and_iff, add_zero, Ne] at ih ⊢
      rw [ih]
      constructor <;>
        · rintro h' h'' rfl
          simp only [imp_false, eq_self_iff_true, not_true, Classical.not_not] at h'
          cases h'
          simp only [not_true, and_false, false_and] at h
#align simple_graph.walk.is_trail.even_countp_edges_iff SimpleGraph.Walk.IsTrail.even_countP_edges_iff

/-- An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma `SimpleGraph.Walk.IsEulerian.IsTrail` shows
that these are trails.

Combine with `p.IsCircuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
def IsEulerian {u v : V} (p : G.Walk u v) : Prop :=
  ∀ e, e ∈ G.edgeSet → p.edges.count e = 1
#align simple_graph.walk.is_eulerian SimpleGraph.Walk.IsEulerian

theorem IsEulerian.isTrail {u v : V} {p : G.Walk u v} (h : p.IsEulerian) : p.IsTrail := by
  rw [isTrail_def, List.nodup_iff_count_le_one]
  intro e
  by_cases he : e ∈ p.edges
  · exact (h e (edges_subset_edgeSet _ he)).le
  · simp [he]
#align simple_graph.walk.is_eulerian.is_trail SimpleGraph.Walk.IsEulerian.isTrail

theorem IsEulerian.mem_edges_iff {u v : V} {p : G.Walk u v} (h : p.IsEulerian) {e : Sym2 V} :
    e ∈ p.edges ↔ e ∈ G.edgeSet :=
  ⟨ fun h => p.edges_subset_edgeSet h
  , fun he => by simpa [Nat.succ_le] using (h e he).ge ⟩
#align simple_graph.walk.is_eulerian.mem_edges_iff SimpleGraph.Walk.IsEulerian.mem_edges_iff

/-- The edge set of an Eulerian graph is finite. -/
def IsEulerian.fintypeEdgeSet {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    Fintype G.edgeSet :=
  Fintype.ofFinset h.isTrail.edgesFinset fun e => by
    simp only [Finset.mem_mk, Multiset.mem_coe, h.mem_edges_iff]
#align simple_graph.walk.is_eulerian.fintype_edge_set SimpleGraph.Walk.IsEulerian.fintypeEdgeSet

theorem IsTrail.isEulerian_of_forall_mem {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (hc : ∀ e, e ∈ G.edgeSet → e ∈ p.edges) : p.IsEulerian := fun e he =>
  List.count_eq_one_of_mem h.edges_nodup (hc e he)
#align simple_graph.walk.is_trail.is_eulerian_of_forall_mem SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem

theorem isEulerian_iff {u v : V} (p : G.Walk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges := by
  constructor
  · intro h
    exact ⟨h.isTrail, fun _ => h.mem_edges_iff.mpr⟩
  · rintro ⟨h, hl⟩
    exact h.isEulerian_of_forall_mem hl
#align simple_graph.walk.is_eulerian_iff SimpleGraph.Walk.isEulerian_iff

theorem IsEulerian.edgesFinset_eq [Fintype G.edgeSet] {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) : h.isTrail.edgesFinset = G.edgeFinset := by
  ext e
  simp [h.mem_edges_iff]
#align simple_graph.walk.is_eulerian.edges_finset_eq SimpleGraph.Walk.IsEulerian.edgesFinset_eq

theorem IsEulerian.even_degree_iff {x u v : V} {p : G.Walk u v} (ht : p.IsEulerian) [Fintype V]
    [DecidableRel G.Adj] : Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  convert ht.isTrail.even_countP_edges_iff x
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter, ← card_incidenceFinset_eq_degree]
  change Multiset.card _ = _
  congr 1
  convert_to _ = (ht.isTrail.edgesFinset.filter (Membership.mem x)).val
  have : Fintype G.edgeSet := fintypeEdgeSet ht
  rw [ht.edgesFinset_eq, G.incidenceFinset_eq_filter x]
#align simple_graph.walk.is_eulerian.even_degree_iff SimpleGraph.Walk.IsEulerian.even_degree_iff

theorem IsEulerian.card_filter_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V}
    {p : G.Walk u v} (ht : p.IsEulerian) {s}
    (h : s = (Finset.univ : Finset V).filter fun v => Odd (G.degree v)) :
    s.card = 0 ∨ s.card = 2 := by
  subst s
  simp only [Nat.odd_iff_not_even, Finset.card_eq_zero]
  simp only [ht.even_degree_iff, Ne, not_forall, not_and, Classical.not_not, exists_prop]
  obtain rfl | hn := eq_or_ne u v
  · left
    simp
  · right
    convert_to _ = ({u, v} : Finset V).card
    · simp [hn]
    · congr
      ext x
      simp [hn, imp_iff_not_or]
#align simple_graph.walk.is_eulerian.card_filter_odd_degree SimpleGraph.Walk.IsEulerian.card_filter_odd_degree

theorem IsEulerian.card_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
    (ht : p.IsEulerian) : Fintype.card { v : V | Odd (G.degree v) } = 0 ∨
      Fintype.card { v : V | Odd (G.degree v) } = 2 := by
  rw [← Set.toFinset_card]
  apply IsEulerian.card_filter_odd_degree ht
  ext v
  simp
#align simple_graph.walk.is_eulerian.card_odd_degree SimpleGraph.Walk.IsEulerian.card_odd_degree

end Walk

end SimpleGraph
