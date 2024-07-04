/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Nat.Lattice

#align_import combinatorics.simple_graph.metric from "leanprover-community/mathlib"@"352ecfe114946c903338006dd3287cb5a9955ff2"

/-!
# Graph metric

This module defines the `SimpleGraph.dist` function, which takes
pairs of vertices to the length of the shortest walk between them.

## Main definitions

- `SimpleGraph.dist` is the graph metric.

## Todo

- Provide an additional computable version of `SimpleGraph.dist`
  for when `G` is connected.

- Evaluate `Nat` vs `ENat` for the codomain of `dist`, or potentially
  having an additional `edist` when the objects under consideration are
  disconnected graphs.

- When directed graphs exist, a directed notion of distance,
  likely `ENat`-valued.

## Tags

graph metric, distance

-/


namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ## Metric -/


/-- The distance between two vertices is the length of the shortest walk between them.
If no such walk exists, this uses the junk value of `0`. -/
noncomputable def dist (u v : V) : ℕ :=
  sInf (Set.range (Walk.length : G.Walk u v → ℕ))
#align simple_graph.dist SimpleGraph.dist

variable {G}

protected theorem Reachable.exists_walk_of_dist {u v : V} (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)
#align simple_graph.reachable.exists_walk_of_dist SimpleGraph.Reachable.exists_walk_of_dist

protected theorem Connected.exists_walk_of_dist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  (hconn u v).exists_walk_of_dist
#align simple_graph.connected.exists_walk_of_dist SimpleGraph.Connected.exists_walk_of_dist

theorem dist_le {u v : V} (p : G.Walk u v) : G.dist u v ≤ p.length :=
  Nat.sInf_le ⟨p, rfl⟩
#align simple_graph.dist_le SimpleGraph.dist_le

@[simp]
theorem dist_eq_zero_iff_eq_or_not_reachable {u v : V} :
    G.dist u v = 0 ↔ u = v ∨ ¬G.Reachable u v := by simp [dist, Nat.sInf_eq_zero, Reachable]
#align simple_graph.dist_eq_zero_iff_eq_or_not_reachable SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable

theorem dist_self {v : V} : dist G v v = 0 := by simp
#align simple_graph.dist_self SimpleGraph.dist_self

protected theorem Reachable.dist_eq_zero_iff {u v : V} (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by simp [hr]
#align simple_graph.reachable.dist_eq_zero_iff SimpleGraph.Reachable.dist_eq_zero_iff

protected theorem Reachable.pos_dist_of_ne {u v : V} (h : G.Reachable u v) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by simp [h, hne])
#align simple_graph.reachable.pos_dist_of_ne SimpleGraph.Reachable.pos_dist_of_ne

protected theorem Connected.dist_eq_zero_iff (hconn : G.Connected) {u v : V} :
    G.dist u v = 0 ↔ u = v := by simp [hconn u v]
#align simple_graph.connected.dist_eq_zero_iff SimpleGraph.Connected.dist_eq_zero_iff

protected theorem Connected.pos_dist_of_ne {u v : V} (hconn : G.Connected) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by intro h; exact False.elim (hne (hconn.dist_eq_zero_iff.mp h)))
#align simple_graph.connected.pos_dist_of_ne SimpleGraph.Connected.pos_dist_of_ne

theorem dist_eq_zero_of_not_reachable {u v : V} (h : ¬G.Reachable u v) : G.dist u v = 0 := by
  simp [h]
#align simple_graph.dist_eq_zero_of_not_reachable SimpleGraph.dist_eq_zero_of_not_reachable

theorem nonempty_of_pos_dist {u v : V} (h : 0 < G.dist u v) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  simpa [Set.range_nonempty_iff_nonempty, Set.nonempty_iff_univ_nonempty] using
    Nat.nonempty_of_pos_sInf h
#align simple_graph.nonempty_of_pos_dist SimpleGraph.nonempty_of_pos_dist

protected theorem Connected.dist_triangle (hconn : G.Connected) {u v w : V} :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_of_dist u v
  obtain ⟨q, hq⟩ := hconn.exists_walk_of_dist v w
  rw [← hp, ← hq, ← Walk.length_append]
  apply dist_le
#align simple_graph.connected.dist_triangle SimpleGraph.Connected.dist_triangle

private theorem dist_comm_aux {u v : V} (h : G.Reachable u v) : G.dist u v ≤ G.dist v u := by
  obtain ⟨p, hp⟩ := h.symm.exists_walk_of_dist
  rw [← hp, ← Walk.length_reverse]
  apply dist_le

theorem dist_comm {u v : V} : G.dist u v = G.dist v u := by
  by_cases h : G.Reachable u v
  · apply le_antisymm (dist_comm_aux h) (dist_comm_aux h.symm)
  · have h' : ¬G.Reachable v u := fun h' => absurd h'.symm h
    simp [h, h', dist_eq_zero_of_not_reachable]
#align simple_graph.dist_comm SimpleGraph.dist_comm

lemma dist_ne_zero_iff_ne_and_reachable {u v : V} : G.dist u v ≠ 0 ↔ u ≠ v ∧ G.Reachable u v := by
  rw [ne_eq, dist_eq_zero_iff_eq_or_not_reachable.not]
  push_neg; rfl

lemma Reachable.of_dist_ne_zero {u v : V} (h : G.dist u v ≠ 0) : G.Reachable u v :=
  (dist_ne_zero_iff_ne_and_reachable.mp h).2

lemma exists_walk_of_dist_ne_zero {u v : V} (h : G.dist u v ≠ 0) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  (Reachable.of_dist_ne_zero h).exists_walk_of_dist

/- The distance between vertices is equal to `1` if and only if these vertices are adjacent. -/
theorem dist_eq_one_iff_adj {u v : V} : G.dist u v = 1 ↔ G.Adj u v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let ⟨w, hw⟩ := exists_walk_of_dist_ne_zero <| ne_zero_of_eq_one h
    exact w.adj_of_length_eq_one <| h ▸ hw
  · have : h.toWalk.length = 1 := Walk.length_cons _ _
    exact ge_antisymm (h.reachable.pos_dist_of_ne h.ne) (this ▸ dist_le _)

theorem Walk.isPath_of_length_eq_dist {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v) :
    p.IsPath := by
  classical
  have : p.bypass = p := by
    apply Walk.bypass_eq_self_of_length_le
    calc p.length
      _ = G.dist u v := hp
      _ ≤ p.bypass.length := dist_le p.bypass
  rw [← this]
  apply Walk.bypass_isPath

lemma Reachable.exists_path_of_dist {u v : V} (hr : G.Reachable u v) :
    ∃ (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v := by
  obtain ⟨p, h⟩ := hr.exists_walk_of_dist
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

lemma Connected.exists_path_of_dist (hconn : G.Connected) (u v : V) :
    ∃ (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v := by
  obtain ⟨p, h⟩ := hconn.exists_walk_of_dist u v
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

end SimpleGraph
