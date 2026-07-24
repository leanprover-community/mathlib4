/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Paths

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

@[expose] public section


namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v x : V}

namespace Walk

/-- The edges of a trail as a finset, since each edge in a trail appears exactly once. -/
abbrev IsTrail.edgesFinset {p : G.Walk u v} (h : p.IsTrail) : Finset (Sym2 V) :=
  ⟨p.edges, h.edges_nodup⟩

variable [DecidableEq V]

theorem IsTrail.even_countP_edges_iff {p : G.Walk u v} (ht : p.IsTrail) (x : V) :
    Even (p.edges.countP fun e ↦ x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  induction p with
  | nil => simp
  | cons huv p ih => grind [isTrail_cons, edges_cons, G.irrefl]

/-- An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma `SimpleGraph.Walk.IsEulerian.IsTrail` shows
that these are trails.

Combine with `p.IsCircuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
def IsEulerian (p : G.Walk u v) : Prop :=
  ∀ e, e ∈ G.edgeSet → p.edges.count e = 1

theorem IsEulerian.isTrail {p : G.Walk u v} (h : p.IsEulerian) : p.IsTrail := by
  rw [isTrail_def, List.nodup_iff_count_eq_one]
  exact (h · <| p.edges_subset_edgeSet ·)

theorem IsEulerian.mem_edges_iff {p : G.Walk u v} (h : p.IsEulerian) {e : Sym2 V} :
    e ∈ p.edges ↔ e ∈ G.edgeSet :=
  ⟨fun h ↦ p.edges_subset_edgeSet h, fun he ↦ by simpa using (h e he).ge⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The edge set of an Eulerian graph is finite. -/
@[instance_reducible]
def IsEulerian.fintypeEdgeSet {p : G.Walk u v} (h : p.IsEulerian) : Fintype G.edgeSet :=
  .ofFinset h.isTrail.edgesFinset <| by simp [h.mem_edges_iff]

theorem IsTrail.isEulerian_of_forall_mem {p : G.Walk u v} (h : p.IsTrail)
    (hc : ∀ e, e ∈ G.edgeSet → e ∈ p.edges) : p.IsEulerian :=
  fun e he ↦ List.count_eq_one_of_mem h.edges_nodup (hc e he)

theorem isEulerian_iff (p : G.Walk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges where
  mp h := ⟨h.isTrail, fun _ ↦ h.mem_edges_iff.mpr⟩
  mpr := fun ⟨h, hl⟩ ↦ h.isEulerian_of_forall_mem hl

theorem IsTrail.isEulerian_iff {p : G.Walk u v} (hp : p.IsTrail) :
    p.IsEulerian ↔ p.edgeSet = G.edgeSet where
  mp h := p.edgeSet_subset_edgeSet.antisymm (p.isEulerian_iff.mp h).2
  mpr h := p.isEulerian_iff.mpr ⟨hp, by simp [← h]⟩

theorem IsEulerian.edgeSet_eq {p : G.Walk u v} (h : p.IsEulerian) : p.edgeSet = G.edgeSet := by
  rwa [← h.isTrail.isEulerian_iff]

set_option backward.isDefEq.respectTransparency.types false in
theorem IsEulerian.edgesFinset_eq [Fintype G.edgeSet] {p : G.Walk u v} (h : p.IsEulerian) :
    h.isTrail.edgesFinset = G.edgeFinset := by
  ext e
  simp [h.mem_edges_iff]

theorem IsEulerian.even_degree_iff {p : G.Walk u v} (ht : p.IsEulerian) [Fintype V]
    [DecidableRel G.Adj] : Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  rw [← ht.isTrail.even_countP_edges_iff, ← Multiset.coe_countP, Multiset.countP_eq_card_filter,
    ← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter, ← ht.edgesFinset_eq]
  simp [Finset.card_def]

theorem IsEulerian.card_filter_odd_degree [Fintype V] [DecidableRel G.Adj]
    {p : G.Walk u v} (ht : p.IsEulerian) {s} (h : s = ({ v | Odd (G.degree v) } : Finset V)) :
    s.card = 0 ∨ s.card = 2 := by
  subst s
  simp_rw [← Nat.not_even_iff_odd, ht.even_degree_iff]
  obtain rfl | hn := eq_or_ne u v
  · simp
  · grind [Finset.card_pair hn, congrArg Finset.card]

theorem IsEulerian.card_odd_degree [Fintype V] [DecidableRel G.Adj] {p : G.Walk u v}
    (ht : p.IsEulerian) :
    Fintype.card { v | Odd (G.degree v) } = 0 ∨ Fintype.card { v | Odd (G.degree v) } = 2 := by
  rw [← Set.toFinset_card]
  apply ht.card_filter_odd_degree
  simp

end Walk

end SimpleGraph
