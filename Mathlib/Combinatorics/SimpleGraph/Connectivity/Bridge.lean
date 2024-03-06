/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.CircuitCycle
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Basic

/-!
# Bridge edges

An edge of a graph is a bridge if removing it disconnects the graph (i.e. the edge's endpoints
cannot reach one another).

## Main statements

* `SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_mem` characterizes bridge edges in terms of
  there being no cycle containing them.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

/-- An edge of a graph is a *bridge* if, after removing it, its incident vertices
are no longer reachable from one another. -/
def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧
    Sym2.lift ⟨fun v w => ¬(G \ fromEdgeSet {e}).Reachable v w, by simp [reachable_comm]⟩ e
#align simple_graph.is_bridge SimpleGraph.IsBridge

theorem isBridge_iff :
    G.IsBridge s(u, v) ↔ G.Adj u v ∧ ¬(G \ fromEdgeSet {s(u, v)}).Reachable u v := Iff.rfl
#align simple_graph.is_bridge_iff SimpleGraph.isBridge_iff

theorem reachable_delete_edges_iff_exists_walk :
    (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔ ∃ p : G.Walk v w, ¬s(v, w) ∈ p.edges := by
  constructor
  · rintro ⟨p⟩
    use p.map (Hom.mapSpanningSubgraphs (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.mapSpanningSubgraphs_apply, Sym2.map_id', id.def]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_diff,
      Set.mem_singleton_iff]
    exact ⟨p.edges_subset_edgeSet ep, fun h' => h (h' ▸ ep)⟩
#align simple_graph.reachable_delete_edges_iff_exists_walk SimpleGraph.reachable_delete_edges_iff_exists_walk

theorem isBridge_iff_adj_and_forall_walk_mem_edges :
    G.IsBridge s(v, w) ↔ G.Adj v w ∧ ∀ p : G.Walk v w, s(v, w) ∈ p.edges := by
  rw [isBridge_iff, and_congr_right']
  rw [reachable_delete_edges_iff_exists_walk, not_exists_not]
#align simple_graph.is_bridge_iff_adj_and_forall_walk_mem_edges SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges

theorem reachable_deleteEdges_iff_exists_cycle.aux [DecidableEq V]
    (hb : ∀ p : G.Walk v w, s(v, w) ∈ p.edges) (c : G.Walk u u) (hc : c.IsTrail)
    (he : s(v, w) ∈ c.edges)
    (hw : w ∈ (c.takeUntil v (c.fst_mem_support_of_mem_edges he)).support) : False := by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  --      puw     pwv     pvu
  --   u ----> w ----> v ----> u
  let puw := (c.takeUntil v hv).takeUntil w hw
  let pwv := (c.takeUntil v hv).dropUntil w hw
  let pvu := c.dropUntil v hv
  have : c = (puw.append pwv).append pvu := by simp [puw, pwv, pvu]
  -- We have two walks from v to w
  --      pvu     puw
  --   v ----> u ----> w
  --   |               ^
  --    `-------------'
  --      pwv.reverse
  -- so they both contain the edge s(v, w), but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw)
  have hpq' := hb pwv.reverse
  rw [Walk.edges_reverse, List.mem_reverse] at hpq'
  rw [Walk.isTrail_def, this, Walk.edges_append, Walk.edges_append, List.nodup_append_comm,
    ← List.append_assoc, ← Walk.edges_append] at hc
  exact List.disjoint_of_nodup_append hc hbq hpq'
#align simple_graph.reachable_delete_edges_iff_exists_cycle.aux SimpleGraph.reachable_deleteEdges_iff_exists_cycle.aux

-- Porting note: the unused variable checker helped eliminate a good amount of this proof (!)
theorem adj_and_reachable_delete_edges_iff_exists_cycle :
    G.Adj v w ∧ (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  rw [reachable_delete_edges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply Path.cons_isCycle
      rw [Sym2.eq_swap]
      intro h
      cases hp (Walk.edges_toPath_subset p h)
    · simp only [Sym2.eq_swap, Walk.edges_cons, List.mem_cons, eq_self_iff_true, true_or_iff]
  · rintro ⟨u, c, hc, he⟩
    refine ⟨c.adj_of_mem_edges he, ?_⟩
    by_contra! hb
    have hb' : ∀ p : G.Walk w v, s(w, v) ∈ p.edges := by
      intro p
      simpa [Sym2.eq_swap] using hb p.reverse
    have hvc : v ∈ c.support := Walk.fst_mem_support_of_mem_edges c he
    refine reachable_deleteEdges_iff_exists_cycle.aux hb' (c.rotate hvc) (hc.isTrail.rotate hvc)
      ?_ (Walk.start_mem_support _)
    rwa [(Walk.rotate_edges c hvc).mem_iff, Sym2.eq_swap]
#align simple_graph.adj_and_reachable_delete_edges_iff_exists_cycle SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle

theorem isBridge_iff_adj_and_forall_cycle_not_mem : G.IsBridge s(v, w) ↔
    G.Adj v w ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → s(v, w) ∉ p.edges := by
  rw [isBridge_iff, and_congr_right_iff]
  intro h
  rw [← not_iff_not]
  push_neg
  rw [← adj_and_reachable_delete_edges_iff_exists_cycle]
  simp only [h, true_and_iff]
#align simple_graph.is_bridge_iff_adj_and_forall_cycle_not_mem SimpleGraph.isBridge_iff_adj_and_forall_cycle_not_mem

theorem isBridge_iff_mem_and_forall_cycle_not_mem {e : Sym2 V} :
    G.IsBridge e ↔ e ∈ G.edgeSet ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges :=
  Sym2.ind (fun _ _ => isBridge_iff_adj_and_forall_cycle_not_mem) e
#align simple_graph.is_bridge_iff_mem_and_forall_cycle_not_mem SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_mem

end SimpleGraph
