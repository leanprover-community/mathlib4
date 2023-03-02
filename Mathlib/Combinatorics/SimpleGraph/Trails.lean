/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module combinatorics.simple_graph.trails
! leanprover-community/mathlib commit edaaaa4a5774e6623e0ddd919b2f2db49c65add4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Connectivity
import Mathbin.Data.Nat.Parity

/-!

# Trails and Eulerian trails

This module contains additional theory about trails, including Eulerian trails (also known
as Eulerian circuits).

## Main definitions

* `simple_graph.walk.is_eulerian` is the predicate that a trail is an Eulerian trail.
* `simple_graph.walk.is_trail.even_countp_edges_iff` gives a condition on the number of edges
  in a trail that can be incident to a given vertex.
* `simple_graph.walk.is_eulerian.even_degree_iff` gives a condition on the degrees of vertices
  when there exists an Eulerian trail.
* `simple_graph.walk.is_eulerian.card_odd_degree` gives the possible numbers of odd-degree
  vertices when there exists an Eulerian trail.

## Todo

* Prove that there exists an Eulerian trail when the conclusion to
  `simple_graph.walk.is_eulerian.card_odd_degree` holds.

## Tags

Eulerian trails

-/


namespace SimpleGraph

variable {V : Type _} {G : SimpleGraph V}

namespace Walk

/-- The edges of a trail as a finset, since each edge in a trail appears exactly once. -/
@[reducible]
def IsTrail.edgesFinset {u v : V} {p : G.Walk u v} (h : p.IsTrail) : Finset (Sym2 V) :=
  ⟨p.edges, h.edges_nodup⟩
#align simple_graph.walk.is_trail.edges_finset SimpleGraph.Walk.IsTrail.edgesFinset

variable [DecidableEq V]

theorem IsTrail.even_countp_edges_iff {u v : V} {p : G.Walk u v} (ht : p.IsTrail) (x : V) :
    Even (p.edges.countp fun e => x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v :=
  by
  induction' p with u u v w huv p ih
  · simp
  · rw [cons_is_trail_iff] at ht
    specialize ih ht.1
    simp only [List.countp_cons, Ne.def, edges_cons, Sym2.mem_iff]
    split_ifs with h
    · obtain rfl | rfl := h
      · rw [Nat.even_add_one, ih]
        simp only [huv.ne, imp_false, Ne.def, not_false_iff, true_and_iff, not_forall,
          Classical.not_not, exists_prop, eq_self_iff_true, not_true, false_and_iff,
          and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless _ huv
      · rw [Nat.even_add_one, ih, ← not_iff_not]
        simp only [huv.ne.symm, Ne.def, eq_self_iff_true, not_true, false_and_iff, not_forall,
          not_false_iff, exists_prop, and_true_iff, Classical.not_not, true_and_iff, iff_and_self]
        rintro rfl
        exact huv.ne
    · rw [not_or] at h
      simp only [h.1, h.2, not_false_iff, true_and_iff, add_zero, Ne.def] at ih⊢
      rw [ih]
      constructor <;>
        · rintro h' h'' rfl
          simp only [imp_false, eq_self_iff_true, not_true, Classical.not_not] at h'
          cases h'
          simpa using h
#align simple_graph.walk.is_trail.even_countp_edges_iff SimpleGraph.Walk.IsTrail.even_countp_edges_iff

/-- An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma `simple_graph.walk.is_eulerian.is_trail` shows
that these are trails.

Combine with `p.is_circuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
def IsEulerian {u v : V} (p : G.Walk u v) : Prop :=
  ∀ e, e ∈ G.edgeSetEmbedding → p.edges.count e = 1
#align simple_graph.walk.is_eulerian SimpleGraph.Walk.IsEulerian

theorem IsEulerian.isTrail {u v : V} {p : G.Walk u v} (h : p.IsEulerian) : p.IsTrail :=
  by
  rw [is_trail_def, List.nodup_iff_count_le_one]
  intro e
  by_cases he : e ∈ p.edges
  · exact (h e (edges_subset_edge_set _ he)).le
  · simp [he]
#align simple_graph.walk.is_eulerian.is_trail SimpleGraph.Walk.IsEulerian.isTrail

theorem IsEulerian.mem_edges_iff {u v : V} {p : G.Walk u v} (h : p.IsEulerian) {e : Sym2 V} :
    e ∈ p.edges ↔ e ∈ G.edgeSetEmbedding :=
  ⟨fun h => p.edges_subset_edgeSet h, fun he => by simpa using (h e he).ge⟩
#align simple_graph.walk.is_eulerian.mem_edges_iff SimpleGraph.Walk.IsEulerian.mem_edges_iff

/-- The edge set of an Eulerian graph is finite. -/
def IsEulerian.fintypeEdgeSet {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    Fintype G.edgeSetEmbedding :=
  Fintype.ofFinset h.IsTrail.edgesFinset fun e => by
    simp only [Finset.mem_mk, Multiset.mem_coe, h.mem_edges_iff]
#align simple_graph.walk.is_eulerian.fintype_edge_set SimpleGraph.Walk.IsEulerian.fintypeEdgeSet

theorem IsTrail.isEulerian_of_forall_mem {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (hc : ∀ e, e ∈ G.edgeSetEmbedding → e ∈ p.edges) : p.IsEulerian := fun e he =>
  List.count_eq_one_of_mem h.edges_nodup (hc e he)
#align simple_graph.walk.is_trail.is_eulerian_of_forall_mem SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem

theorem isEulerian_iff {u v : V} (p : G.Walk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.edgeSetEmbedding → e ∈ p.edges :=
  by
  constructor
  · intro h
    exact ⟨h.is_trail, fun _ => h.mem_edges_iff.mpr⟩
  · rintro ⟨h, hl⟩
    exact h.is_eulerian_of_forall_mem hl
#align simple_graph.walk.is_eulerian_iff SimpleGraph.Walk.isEulerian_iff

theorem IsEulerian.edgesFinset_eq [Fintype G.edgeSetEmbedding] {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) : h.IsTrail.edgesFinset = G.edgeFinset :=
  by
  ext e
  simp [h.mem_edges_iff]
#align simple_graph.walk.is_eulerian.edges_finset_eq SimpleGraph.Walk.IsEulerian.edgesFinset_eq

theorem IsEulerian.even_degree_iff {x u v : V} {p : G.Walk u v} (ht : p.IsEulerian) [Fintype V]
    [DecidableRel G.Adj] : Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v :=
  by
  convert ht.is_trail.even_countp_edges_iff x
  rw [← Multiset.coe_countp, Multiset.countp_eq_card_filter, ← card_incidence_finset_eq_degree]
  change Multiset.card _ = _
  congr 1
  convert_to _ = (ht.is_trail.edges_finset.filter (Membership.Mem x)).val
  rw [ht.edges_finset_eq, G.incidence_finset_eq_filter x]
#align simple_graph.walk.is_eulerian.even_degree_iff SimpleGraph.Walk.IsEulerian.even_degree_iff

theorem IsEulerian.card_filter_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V}
    {p : G.Walk u v} (ht : p.IsEulerian) {s}
    (h : s = (Finset.univ : Finset V).filterₓ fun v => Odd (G.degree v)) :
    s.card = 0 ∨ s.card = 2 := by
  subst s
  simp only [Nat.odd_iff_not_even, Finset.card_eq_zero]
  simp only [ht.even_degree_iff, Ne.def, not_forall, not_and, Classical.not_not, exists_prop]
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
    (ht : p.IsEulerian) :
    Fintype.card { v : V | Odd (G.degree v) } = 0 ∨ Fintype.card { v : V | Odd (G.degree v) } = 2 :=
  by
  rw [← Set.toFinset_card]
  apply is_eulerian.card_filter_odd_degree ht
  ext v
  simp
#align simple_graph.walk.is_eulerian.card_odd_degree SimpleGraph.Walk.IsEulerian.card_odd_degree

end Walk

end SimpleGraph

