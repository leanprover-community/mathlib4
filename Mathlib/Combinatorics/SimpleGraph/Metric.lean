/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara, Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.ENat.Lattice

#align_import combinatorics.simple_graph.metric from "leanprover-community/mathlib"@"352ecfe114946c903338006dd3287cb5a9955ff2"

/-!
# Graph metric

This module defines the `SimpleGraph.edist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `SimpleGraph.dist`
which is the `ℕ`-valued version of `SimpleGraph.edist`.

## Main definitions

- `SimpleGraph.dist` is the graph extended metric.
- `SimpleGraph.dist` is the graph metric.

## Todo

- Provide an additional computable version of `SimpleGraph.dist`
  for when `G` is connected.

- When directed graphs exist, a directed notion of distance,
  likely `ENat`-valued.

## Tags

graph metric, distance

-/


namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ## Metric -/

section edist

noncomputable def edist (u v : V) : ℕ∞ :=
  ⨅ w : G.Walk u v, w.length

variable {G} {u v : V}

protected theorem Reachable.exists_walk_of_edist {u v : V} (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  csInf_mem <| Set.range_nonempty_iff_nonempty.mpr hr

protected theorem Connected.exists_walk_of_edist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (hconn u v).exists_walk_of_edist

theorem edist_le {u v : V} (p : G.Walk u v) :
    G.edist u v ≤ p.length :=
  sInf_le ⟨p, rfl⟩

@[simp]
theorem edist_eq_zero_iff_eq {u v : V} :
    G.edist u v = 0 ↔ u = v := by
  apply Iff.intro <;> simp [edist, ENat.iInf_eq_zero]

theorem edist_self {v : V} : edist G v v = 0 :=
  edist_eq_zero_iff_eq.mpr rfl

theorem pos_edist_of_ne {u v : V} (hne : u ≠ v) :
    0 < G.edist u v :=
  pos_iff_ne_zero.mpr <| edist_eq_zero_iff_eq.ne.mpr hne

lemma edist_eq_top_of_not_reachable (h : ¬G.Reachable u v) :
    G.edist u v = ⊤ := by
  simp [edist, not_reachable_iff_isEmplty_walk.mp h]

theorem Reachable.of_edist_ne_top {u v : V} (h : G.edist u v ≠ ⊤) :
    G.Reachable u v :=
  not_not.mp <| edist_eq_top_of_not_reachable.mt h

protected theorem Connected.edist_triangle (hconn : G.Connected) {u v w : V} :
    G.edist u w ≤ G.edist u v + G.edist v w := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_of_edist u v
  obtain ⟨q, hq⟩ := hconn.exists_walk_of_edist v w
  rw [← hp, ← hq, ← Nat.cast_add, ← Walk.length_append]
  apply edist_le

theorem edist_comm {u v : V} : G.edist u v = G.edist v u := by
  have {u v : V} (h : G.Reachable u v) : G.edist u v ≤ G.edist v u := by
    obtain ⟨p, hp⟩ := h.symm.exists_walk_of_edist
    rw [← hp, ← Walk.length_reverse]
    apply edist_le
  by_cases h : G.Reachable u v
  · apply le_antisymm (this h) (this h.symm)
  · have h' : ¬G.Reachable v u := fun h' => absurd h'.symm h
    simp [h, h', edist_eq_top_of_not_reachable]

lemma exists_walk_of_edist_ne_top {u v : V} (h : G.edist u v ≠ ⊤) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (Reachable.of_edist_ne_top h).exists_walk_of_edist

/--
The extended distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
theorem edist_eq_one_iff_adj {u v : V} : G.edist u v = 1 ↔ G.Adj u v := by
  have ne_top_of_eq_one {n : ℕ∞} (h : n = 1) : n ≠ ⊤ := by
    rw [← ENat.coe_toNat_eq_self, h]; rfl
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let ⟨w, hw⟩ := exists_walk_of_edist_ne_top <| ne_top_of_eq_one h
    rw [h, Nat.cast_eq_one] at hw
    exact w.adj_of_length_eq_one <| hw
  · exact ge_antisymm (ENat.one_le_iff_pos.mpr <| pos_edist_of_ne h.ne) <| edist_le h.toWalk

end edist

section dist

noncomputable def dist (u v : V) : ℕ :=
  (G.edist u v).toNat
#align simple_graph.dist SimpleGraph.dist

variable {G} {u v : V}

theorem dist_eq_sInf : G.dist u v = sInf (Set.range (Walk.length : G.Walk u v → ℕ)) :=
  ENat.iInf_toNat

protected theorem Reachable.exists_walk_of_dist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)
#align simple_graph.reachable.exists_walk_of_dist SimpleGraph.Reachable.exists_walk_of_dist

protected theorem Connected.exists_walk_of_dist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ (hconn u v).exists_walk_of_dist
#align simple_graph.connected.exists_walk_of_dist SimpleGraph.Connected.exists_walk_of_dist

theorem dist_le (p : G.Walk u v) : G.dist u v ≤ p.length :=
  dist_eq_sInf ▸ Nat.sInf_le ⟨p, rfl⟩
#align simple_graph.dist_le SimpleGraph.dist_le

@[simp]
theorem dist_eq_zero_iff_eq_or_not_reachable :
    G.dist u v = 0 ↔ u = v ∨ ¬G.Reachable u v := by simp [dist_eq_sInf, Nat.sInf_eq_zero, Reachable]
#align simple_graph.dist_eq_zero_iff_eq_or_not_reachable SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable

theorem dist_self : dist G v v = 0 := by simp
#align simple_graph.dist_self SimpleGraph.dist_self

protected theorem Reachable.dist_eq_zero_iff (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by simp [hr]
#align simple_graph.reachable.dist_eq_zero_iff SimpleGraph.Reachable.dist_eq_zero_iff

protected theorem Reachable.pos_dist_of_ne (h : G.Reachable u v) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by simp [h, hne])
#align simple_graph.reachable.pos_dist_of_ne SimpleGraph.Reachable.pos_dist_of_ne

protected theorem Connected.dist_eq_zero_iff (hconn : G.Connected) {u v : V} :
    G.dist u v = 0 ↔ u = v := by simp [hconn u v]
#align simple_graph.connected.dist_eq_zero_iff SimpleGraph.Connected.dist_eq_zero_iff

protected theorem Connected.pos_dist_of_ne {u v : V} (hconn : G.Connected) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero fun h ↦ False.elim <| hne <| (hconn.dist_eq_zero_iff).mp h
#align simple_graph.connected.pos_dist_of_ne SimpleGraph.Connected.pos_dist_of_ne

theorem dist_eq_zero_of_not_reachable {u v : V} (h : ¬G.Reachable u v) : G.dist u v = 0 := by
  simp [h]
#align simple_graph.dist_eq_zero_of_not_reachable SimpleGraph.dist_eq_zero_of_not_reachable

theorem nonempty_of_pos_dist {u v : V} (h : 0 < G.dist u v) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [dist_eq_sInf] at h
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

end dist

end SimpleGraph
