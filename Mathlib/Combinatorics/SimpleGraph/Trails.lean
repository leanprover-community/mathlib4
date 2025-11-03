/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Paths

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

## TODO

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

variable [DecidableEq V]

theorem IsTrail.even_countP_edges_iff {u v : V} {p : G.Walk u v} (ht : p.IsTrail) (x : V) :
    Even (p.edges.countP fun e => x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  induction p with
  | nil => simp
  | cons huv p ih =>
    rw [cons_isTrail_iff] at ht
    specialize ih ht.1
    simp only [List.countP_cons, Ne, edges_cons, Sym2.mem_iff]
    split_ifs with h
    · rw [decide_eq_true_eq] at h
      obtain (rfl | rfl) := h
      · rw [Nat.even_add_one, ih]
        simp only [huv.ne, imp_false, Ne, not_false_iff, true_and, not_forall,
          Classical.not_not, exists_prop, not_true, false_and,
          and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless _ huv
      · rw [Nat.even_add_one, ih, ← not_iff_not]
        simp only [huv.ne.symm, Ne, not_true, false_and, not_forall,
          not_false_iff, exists_prop, and_true, Classical.not_not, true_and, iff_and_self]
        rintro rfl
        exact huv.ne
    · grind

/-- An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma `SimpleGraph.Walk.IsEulerian.IsTrail` shows
that these are trails.

Combine with `p.IsCircuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
def IsEulerian {u v : V} (p : G.Walk u v) : Prop :=
  ∀ e, e ∈ G.edgeSet → p.edges.count e = 1

theorem IsEulerian.isTrail {u v : V} {p : G.Walk u v} (h : p.IsEulerian) : p.IsTrail := by
  rw [isTrail_def, List.nodup_iff_count_le_one]
  intro e
  by_cases he : e ∈ p.edges
  · exact (h e (edges_subset_edgeSet _ he)).le
  · simp [List.count_eq_zero_of_not_mem he]

theorem IsEulerian.mem_edges_iff {u v : V} {p : G.Walk u v} (h : p.IsEulerian) {e : Sym2 V} :
    e ∈ p.edges ↔ e ∈ G.edgeSet :=
  ⟨fun h => p.edges_subset_edgeSet h,
   fun he => by simpa [Nat.succ_le_iff] using (h e he).ge⟩

/-- The edge set of an Eulerian graph is finite. -/
def IsEulerian.fintypeEdgeSet {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    Fintype G.edgeSet :=
  Fintype.ofFinset h.isTrail.edgesFinset fun e => by
    simp only [Finset.mem_mk, Multiset.mem_coe, h.mem_edges_iff]

theorem IsTrail.isEulerian_of_forall_mem {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (hc : ∀ e, e ∈ G.edgeSet → e ∈ p.edges) : p.IsEulerian := fun e he =>
  List.count_eq_one_of_mem h.edges_nodup (hc e he)

theorem isEulerian_iff {u v : V} (p : G.Walk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges := by
  constructor
  · intro h
    exact ⟨h.isTrail, fun _ => h.mem_edges_iff.mpr⟩
  · rintro ⟨h, hl⟩
    exact h.isEulerian_of_forall_mem hl

theorem IsTrail.isEulerian_iff {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.IsEulerian ↔ p.edgeSet = G.edgeSet :=
  ⟨fun h ↦ Set.Subset.antisymm p.edges_subset_edgeSet (p.isEulerian_iff.mp h).2,
   fun h ↦ p.isEulerian_iff.mpr ⟨hp, by simp [← h]⟩⟩

theorem IsEulerian.edgeSet_eq {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    p.edgeSet = G.edgeSet := by
  rwa [← h.isTrail.isEulerian_iff]

theorem IsEulerian.edgesFinset_eq [Fintype G.edgeSet] {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) : h.isTrail.edgesFinset = G.edgeFinset := by
  ext e
  simp [h.mem_edges_iff]

theorem IsEulerian.even_degree_iff {x u v : V} {p : G.Walk u v} (ht : p.IsEulerian) [Fintype V]
    [DecidableRel G.Adj] : Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  convert ht.isTrail.even_countP_edges_iff x
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter, ← card_incidenceFinset_eq_degree]
  change Multiset.card _ = _
  congr 1
  convert_to _ = (ht.isTrail.edgesFinset.filter (x ∈ ·)).val
  rw [ht.edgesFinset_eq, G.incidenceFinset_eq_filter x]

theorem IsEulerian.card_filter_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V}
    {p : G.Walk u v} (ht : p.IsEulerian) {s}
    (h : s = (Finset.univ : Finset V).filter fun v => Odd (G.degree v)) :
    s.card = 0 ∨ s.card = 2 := by
  subst s
  simp only [← Nat.not_even_iff_odd, Finset.card_eq_zero]
  simp only [ht.even_degree_iff, Ne, not_forall, not_and, Classical.not_not, exists_prop]
  obtain rfl | hn := eq_or_ne u v
  · simp
  · right
    convert_to _ = ({u, v} : Finset V).card
    · simp [hn]
    · congr
      ext x
      simp [hn, imp_iff_not_or]

theorem IsEulerian.card_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
    (ht : p.IsEulerian) : Fintype.card { v : V | Odd (G.degree v) } = 0 ∨
      Fintype.card { v : V | Odd (G.degree v) } = 2 := by
  rw [← Set.toFinset_card]
  apply IsEulerian.card_filter_odd_degree ht
  ext v
  simp

end Walk

end SimpleGraph
