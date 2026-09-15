/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

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

variable {V : Type*} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v}

namespace Walk

/-- The edges of a trail as a finset, since each edge in a trail appears exactly once. -/
abbrev IsTrail.edgesFinset (h : p.IsTrail) : Finset (Sym2 V) :=
  ⟨p.edges, Multiset.coe_nodup.mpr h.edges_nodup⟩

variable [DecidableEq V]

theorem IsTrail.even_countP_edges_iff (ht : p.IsTrail) (x : V) :
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

theorem IsEulerian.isTrail (h : p.IsEulerian) : p.IsTrail := by
  rw [isTrail_def, List.nodup_iff_count_eq_one]
  exact (h · <| p.edges_subset_edgeSet ·)

theorem IsEulerian.mem_edges_iff (h : p.IsEulerian) {e : Sym2 V} : e ∈ p.edges ↔ e ∈ G.edgeSet :=
  ⟨fun h ↦ p.edges_subset_edgeSet h, fun he ↦ by simpa using (h e he).ge⟩

/-- The edge set of an Eulerian graph is finite. -/
@[instance_reducible]
def IsEulerian.fintypeEdgeSet (h : p.IsEulerian) : Fintype G.edgeSet :=
  .ofFinset h.isTrail.edgesFinset <| by simp [h.mem_edges_iff]

theorem IsTrail.isEulerian_of_forall_mem (h : p.IsTrail) (hc : ∀ e, e ∈ G.edgeSet → e ∈ p.edges) :
    p.IsEulerian :=
  (List.count_eq_one_of_mem h.edges_nodup <| hc · ·)

theorem isEulerian_iff (p : G.Walk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges where
  mp h := ⟨h.isTrail, fun _ ↦ h.mem_edges_iff.mpr⟩
  mpr := fun ⟨h, hl⟩ ↦ h.isEulerian_of_forall_mem hl

theorem IsTrail.isEulerian_iff (hp : p.IsTrail) : p.IsEulerian ↔ p.edgeSet = G.edgeSet where
  mp h := p.edgeSet_subset_edgeSet.antisymm (p.isEulerian_iff.mp h).2
  mpr h := p.isEulerian_iff.mpr ⟨hp, by simp [← h]⟩

theorem IsEulerian.edgeSet_eq (h : p.IsEulerian) : p.edgeSet = G.edgeSet := by
  rwa [← h.isTrail.isEulerian_iff]

theorem IsEulerian.edgesFinset_eq [Fintype G.edgeSet] (h : p.IsEulerian) :
    h.isTrail.edgesFinset = G.edgeFinset := by
  ext e
  simp [h.mem_edges_iff]

theorem IsEulerian.mem_support_of_not_isIsolated (hp : p.IsEulerian) (hw : ¬G.IsIsolated w) :
    w ∈ p.support :=
  have ⟨_, hadj⟩ := exists_adj_iff_not_isIsolated.mpr hw
  p.fst_mem_support_of_mem_edges <| hp.mem_edges_iff.mpr hadj

theorem IsEulerian.nil_iff (hp : p.IsEulerian) : p.Nil ↔ G = ⊥ := by
  simp [← edgeSet_eq_empty, hp.edgeSet_eq]

theorem isEulerian_of_bot (p : Walk ⊥ u v) : p.IsEulerian := by
  intro e h
  simp at h

/-- The support of a non-nil Eulerian trail equals the support of the graph. -/
theorem IsEulerian.mem_support_iff (hp : p.IsEulerian) (hnil : ¬p.Nil) :
    w ∈ p.support ↔ ¬G.IsIsolated w :=
  ⟨fun hwp hw ↦ hnil <| p.nil_of_isIsolated_of_mem_support hw hwp, hp.mem_support_of_not_isIsolated⟩

theorem IsEulerian.connected_of_forall_not_isIsolated (hp : p.IsEulerian)
    (hG : ∀ v, ¬G.IsIsolated v) : G.Connected where
  preconnected a b :=
    have ha : a ∈ p.support := hp.mem_support_of_not_isIsolated <| hG a
    have hb : b ∈ p.support := hp.mem_support_of_not_isIsolated <| hG b
    ⟨p.takeUntil a ha |>.reverse.append <| p.takeUntil b hb⟩
  nonempty := ⟨u⟩

theorem IsEulerian.even_degree_iff (ht : p.IsEulerian) [Fintype V] [DecidableRel G.Adj] :
    Even (G.degree w) ↔ u ≠ v → w ≠ u ∧ w ≠ v := by
  rw [← ht.isTrail.even_countP_edges_iff, ← Multiset.coe_countP, Multiset.countP_eq_card_filter,
    ← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter, ← ht.edgesFinset_eq]
  simp [Finset.card_def]

theorem IsEulerian.card_filter_odd_degree [Fintype V] [DecidableRel G.Adj] (ht : p.IsEulerian) {s}
    (h : s = ({ v | Odd (G.degree v) } : Finset V)) : s.card = 0 ∨ s.card = 2 := by
  subst s
  simp_rw [← Nat.not_even_iff_odd, ht.even_degree_iff]
  obtain rfl | hn := eq_or_ne u v
  · simp
  · grind [Finset.card_pair hn, congrArg Finset.card]

theorem IsEulerian.card_odd_degree [Fintype V] [DecidableRel G.Adj] (ht : p.IsEulerian) :
    Fintype.card { v | Odd (G.degree v) } = 0 ∨ Fintype.card { v | Odd (G.degree v) } = 2 := by
  rw [← Set.toFinset_card]
  apply ht.card_filter_odd_degree
  simp

-- #41524
set_option warn.sorry false in set_option linter.style.longLine false in
theorem _root_.SimpleGraph.Preconnected.exists_isEulerian (h : G.Preconnected) (hp : ∃ (v' : V) (p : G.Walk v' v'), p.IsEulerian) (v : V) : ∃ p : G.Walk v v, p.IsEulerian := sorry

-- #41722
set_option warn.sorry false in set_option linter.style.longLine false in
omit [DecidableEq V] in
theorem edgeSet_mapToSubgraph {u v} {p : G.Walk u v} : p.mapToSubgraph.edgeSet = Sym2.map (↑) ⁻¹' p.edgeSet := sorry

-- #41722
set_option warn.sorry false in set_option linter.style.longLine false in
omit [DecidableEq V] in
theorem isTrail_mapToSubgraph {u v} {p : G.Walk u v} : p.mapToSubgraph.IsTrail ↔ p.IsTrail := sorry

-- TODO: golf `Subgraph.degree_of_notMem_verts` with this
omit [DecidableEq V] in
theorem _root_.SimpleGraph.Subgraph.neighborSet_eq_empty_of_notMem_verts {G' : G.Subgraph} {v : V}
    (hv : v ∉ G'.verts) : G'.neighborSet v = ∅ := by
  grind [Subgraph.mem_neighborSet, Subgraph.Adj.fst_mem]

omit [DecidableEq V] in
theorem _root_.SimpleGraph.Subgraph.mem_verts_of_nonempty_neighborSet {G' : G.Subgraph} {v : V}
    (hv : (G'.neighborSet v).Nonempty) : v ∈ G'.verts := by
  contrapose! hv
  exact G'.neighborSet_eq_empty_of_notMem_verts hv

theorem isEulerian_mapToSubgraph {u v} {p : G.Walk u v} :
    p.mapToSubgraph.IsEulerian ↔ p.IsTrail := by
  rw [isEulerian_iff, isTrail_mapToSubgraph]
  refine ⟨And.left, fun h ↦ ⟨h, fun e he ↦ ?_⟩⟩
  simpa [← edgeSet_mapToSubgraph] using he

omit [DecidableEq V] in
@[simp]
theorem _root_.SimpleGraph.Subgraph.ncard_neighborSet (G' : G.Subgraph) (v)
    [Fintype <| G'.neighborSet v] : (G'.neighborSet v).ncard = G'.degree v := by
  simp_rw [Set.ncard_eq_toFinset_card', Subgraph.finset_card_neighborSet_eq_degree]

omit [DecidableEq V] in
theorem IsTrail.even_ncard_neighborSet_toSubgraph_iff {u v} {p : G.Walk u v}
    (hp : p.IsTrail) (w : V) : Even (p.toSubgraph.neighborSet w).ncard ↔ u ≠ v → w ≠ u ∧ w ≠ v := by
  by_cases! hw : w ∉ p.toSubgraph.verts
  · grind [Subgraph.neighborSet_eq_empty_of_notMem_verts, Set.ncard_empty,
      start_mem_verts_toSubgraph, end_mem_verts_toSubgraph]
  have : Fintype p.toSubgraph.verts := Set.Finite.fintype <| by simp
  classical
  simpa using p.isEulerian_mapToSubgraph.mpr hp |>.even_degree_iff (x := ⟨w, hw⟩)

omit [DecidableEq V] in
theorem IsTrail.even_ncard_neighborSet_toSubgraph {u} {p : G.Walk u u}
    (hp : p.IsTrail) (v : V) : Even (p.toSubgraph.neighborSet v).ncard :=
  hp.even_ncard_neighborSet_toSubgraph_iff v |>.mpr <| by simp

theorem _root_.SimpleGraph.Preconnected.exists_isEulerian_of_even_degree [Fintype V]
    [DecidableRel G.Adj] (hcon : G.Preconnected) (h : ∀ v, Even (G.degree v)) :
    ∀ v, ∃ p : G.Walk v v, p.IsEulerian := by
  -- It suffices to show that there exists an Eulerian trail from some vertex.
  suffices Nonempty V → ∃ (v : V) (p : G.Walk v v), p.IsEulerian from
    fun v ↦ hcon.exists_isEulerian (this ⟨v⟩) v
  intro
  -- Take a longest trail `p` in `G` from `u` to `v`.
  have ⟨u, v, p, hp, hmax⟩ := Walk.exists_isTrail_forall_isTrail_length_le_length G
  -- Since `p` is a trail, it is Eulerian in its own subgraph.
  -- So if the endpoints of `p` differ, then the degree of `u` in `p.toSubgraph` must be odd,
  -- but we know that `u` has even degree so there must be some edge adjacent to `u` in `G` but not
  -- in `p` and so we can extend `p` contradicting its maximality.
  have : u ≠ v → p.toSubgraph.neighborSet u ⊂ G.neighborSet u := by
    grind [hp.even_ncard_neighborSet_toSubgraph_iff, ncard_neighborSet, Subgraph.neighborSet_subset]
  have : u ≠ v → ∃ w, G.Adj u w ∧ s(w, u) ∉ p.edges := by
    grind [adj_toSubgraph_iff_mem_edges, Subgraph.mem_neighborSet, mem_neighborSet]
  have huv : u = v := by
    by_contra! hne
    have ⟨w, hadj, hmem⟩ := this hne
    grind [hp.cons hadj.symm hmem, length_cons]
  subst huv
  -- Now that we've shown that `p` is a closed trail, to show it is Eulerian it suffices to show it
  -- contains every edge. Suppose for the sake of contradiction that `p` misses an edge `(u', v')`.
  refine ⟨u, p, p.isEulerian_iff.mpr ⟨hp, Sym2.ind fun u' v' he ↦ ?_⟩⟩
  by_contra hep
  -- We can assume without loss of generality that this missed edge is incident to `p`:
  wlog hv' : v' ∈ p.support
  · -- Otherwise, since the graph is preconnected there must be a walk from `u` to `v'`.
    have ⟨p'⟩ := hcon u v'
    -- This walk starts with a vertex in `p` and ends at a vertex not in `p`,
    -- so there must exist a boundary dart `d` with one endpoint in `p` and the other not in `p`.
    have ⟨d, hd, hd₁, hd₂⟩ := p'.exists_boundary_dart {v | v ∈ p.support} p.start_mem_support hv'
    -- Thus the edge it represents is also not in `p`, so we can work with it instead of `(u', v')`.
    have hd : s(d.snd, d.fst) ∉ p.edges := fun hmem ↦ hd₂ <| p.fst_mem_support_of_mem_edges hmem
    grind [this (he := d.adj.symm)]
  -- We now have an edge `(u', v')` not in `p` such that `v'` is in `p`, so we can rotate `p` and
  -- extend it with that edge, contradicting the maximality of `p`.
  let p' := p.rotate v' hv' |>.cons he
  have : p'.IsTrail := hp.rotate hv' |>.cons he <| by simpa [p.rotate_edges v' hv' |>.mem_iff]
  grind [length_cons, length_rotate]

end Walk

end SimpleGraph
