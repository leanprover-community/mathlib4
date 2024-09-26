/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara, Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.ENat.Lattice

/-!
# Graph metric

This module defines the `SimpleGraph.edist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `SimpleGraph.dist`
which is the `ℕ`-valued version of `SimpleGraph.edist`.

## Main definitions

- `SimpleGraph.edist` is the graph extended metric.
- `SimpleGraph.dist` is the graph metric.

## TODO

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

/--
The extended distance between two vertices is the length of the shortest walk between them.
It is `⊤` if no such walk exists.
-/
noncomputable def edist (u v : V) : ℕ∞ :=
  ⨅ w : G.Walk u v, w.length

variable {G} {u v w : V}

theorem edist_eq_sInf : G.edist u v = sInf (Set.range fun w : G.Walk u v ↦ (w.length : ℕ∞)) := rfl

protected theorem Reachable.exists_walk_length_eq_edist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  csInf_mem <| Set.range_nonempty_iff_nonempty.mpr hr

protected theorem Connected.exists_walk_length_eq_edist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (hconn u v).exists_walk_length_eq_edist

theorem edist_le (p : G.Walk u v) :
    G.edist u v ≤ p.length :=
  sInf_le ⟨p, rfl⟩
protected alias Walk.edist_le := edist_le

@[simp]
theorem edist_eq_zero_iff :
    G.edist u v = 0 ↔ u = v := by
  apply Iff.intro <;> simp [edist, ENat.iInf_eq_zero]

@[simp]
theorem edist_self : edist G v v = 0 :=
  edist_eq_zero_iff.mpr rfl

theorem edist_pos_of_ne (hne : u ≠ v) :
    0 < G.edist u v :=
  pos_iff_ne_zero.mpr <| edist_eq_zero_iff.ne.mpr hne

lemma edist_eq_top_of_not_reachable (h : ¬G.Reachable u v) :
    G.edist u v = ⊤ := by
  simp [edist, not_reachable_iff_isEmpty_walk.mp h]

theorem reachable_of_edist_ne_top (h : G.edist u v ≠ ⊤) :
    G.Reachable u v :=
  not_not.mp <| edist_eq_top_of_not_reachable.mt h

lemma exists_walk_of_edist_ne_top (h : G.edist u v ≠ ⊤) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (reachable_of_edist_ne_top h).exists_walk_length_eq_edist

protected theorem edist_triangle : G.edist u w ≤ G.edist u v + G.edist v w := by
  cases eq_or_ne (G.edist u v) ⊤ with
  | inl huv => simp [huv]
  | inr huv =>
    cases eq_or_ne (G.edist v w) ⊤ with
    | inl hvw => simp [hvw]
    | inr hvw =>
      obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top huv
      obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top hvw
      rw [← hp, ← hq, ← Nat.cast_add, ← Walk.length_append]
      exact edist_le _

theorem edist_comm : G.edist u v = G.edist v u := by
  rw [edist_eq_sInf, ← Set.image_univ, ← Set.image_univ_of_surjective Walk.reverse_surjective,
    ← Set.image_comp, Set.image_univ, Function.comp_def]
  simp_rw [Walk.length_reverse, ← edist_eq_sInf]

lemma exists_walk_of_edist_eq_coe {k : ℕ} (h : G.edist u v = k) :
    ∃ p : G.Walk u v, p.length = k :=
  have : G.edist u v ≠ ⊤ := by rw [h]; exact ENat.coe_ne_top _
  have ⟨p, hp⟩ := exists_walk_of_edist_ne_top this
  ⟨p, Nat.cast_injective (hp.trans h)⟩

lemma edist_ne_top_iff_reachable : G.edist u v ≠ ⊤ ↔ G.Reachable u v := by
  refine ⟨reachable_of_edist_ne_top, fun h ↦ ?_⟩
  by_contra hx
  simp only [edist, iInf_eq_top, ENat.coe_ne_top] at hx
  exact h.elim hx

/--
The extended distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
theorem edist_eq_one_iff_adj : G.edist u v = 1 ↔ G.Adj u v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top <| by rw [h]; simp
    exact w.adj_of_length_eq_one <| Nat.cast_eq_one.mp <| h ▸ hw
  · exact le_antisymm (edist_le h.toWalk) (Order.one_le_iff_pos.mpr <| edist_pos_of_ne h.ne)

lemma edist_bot_of_ne (h : u ≠ v) : (⊥ : SimpleGraph V).edist u v = ⊤ := by
  rwa [ne_eq, ← reachable_bot.not, ← edist_ne_top_iff_reachable.not, not_not] at h

lemma edist_bot [DecidableEq V] : (⊥ : SimpleGraph V).edist u v = (if u = v then 0 else ⊤) := by
  by_cases h : u = v <;> simp [h, edist_bot_of_ne]

lemma edist_top_of_ne (h : u ≠ v) : (⊤ : SimpleGraph V).edist u v = 1 := by
  simp [h]

lemma edist_top [DecidableEq V] : (⊤ : SimpleGraph V).edist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

/-- Supergraphs have smaller or equal extended distances to their subgraphs. -/
@[gcongr]
theorem edist_anti {G' : SimpleGraph V} (h : G ≤ G') :
    G'.edist u v ≤ G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_edist
    rw [← hw, ← Walk.length_map (Hom.mapSpanningSubgraphs h)]
    apply edist_le
  · exact edist_eq_top_of_not_reachable hr ▸ le_top

end edist

section dist

/--
The distance between two vertices is the length of the shortest walk between them.
If no such walk exists, this uses the junk value of `0`.
-/
noncomputable def dist (u v : V) : ℕ :=
  (G.edist u v).toNat

variable {G} {u v w : V}

theorem dist_eq_sInf : G.dist u v = sInf (Set.range (Walk.length : G.Walk u v → ℕ)) :=
  ENat.iInf_toNat

protected theorem Reachable.exists_walk_length_eq_dist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)

protected theorem Connected.exists_walk_length_eq_dist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ (hconn u v).exists_walk_length_eq_dist

theorem dist_le (p : G.Walk u v) : G.dist u v ≤ p.length :=
  dist_eq_sInf ▸ Nat.sInf_le ⟨p, rfl⟩

@[simp]
theorem dist_eq_zero_iff_eq_or_not_reachable :
    G.dist u v = 0 ↔ u = v ∨ ¬G.Reachable u v := by simp [dist_eq_sInf, Nat.sInf_eq_zero, Reachable]

theorem dist_self : dist G v v = 0 := by simp

protected theorem Reachable.dist_eq_zero_iff (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by simp [hr]

protected theorem Reachable.pos_dist_of_ne (h : G.Reachable u v) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by simp [h, hne])

protected theorem Connected.dist_eq_zero_iff (hconn : G.Connected) :
    G.dist u v = 0 ↔ u = v := by simp [hconn u v]

protected theorem Connected.pos_dist_of_ne (hconn : G.Connected) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero fun h ↦ False.elim <| hne <| (hconn.dist_eq_zero_iff).mp h

theorem dist_eq_zero_of_not_reachable (h : ¬G.Reachable u v) : G.dist u v = 0 := by
  simp [h]

theorem nonempty_of_pos_dist (h : 0 < G.dist u v) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [dist_eq_sInf] at h
  simpa [Set.range_nonempty_iff_nonempty, Set.nonempty_iff_univ_nonempty] using
    Nat.nonempty_of_pos_sInf h

protected theorem Connected.dist_triangle (hconn : G.Connected) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist v w
  rw [← hp, ← hq, ← Walk.length_append]
  apply dist_le

theorem dist_comm : G.dist u v = G.dist v u := by
  rw [dist, dist, edist_comm]

lemma dist_ne_zero_iff_ne_and_reachable : G.dist u v ≠ 0 ↔ u ≠ v ∧ G.Reachable u v := by
  rw [ne_eq, dist_eq_zero_iff_eq_or_not_reachable.not]
  push_neg; rfl

lemma Reachable.of_dist_ne_zero (h : G.dist u v ≠ 0) : G.Reachable u v :=
  (dist_ne_zero_iff_ne_and_reachable.mp h).2

lemma exists_walk_of_dist_ne_zero (h : G.dist u v ≠ 0) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  (Reachable.of_dist_ne_zero h).exists_walk_length_eq_dist

/--
The distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
theorem dist_eq_one_iff_adj : G.dist u v = 1 ↔ G.Adj u v := by
  rw [dist, ENat.toNat_eq_iff, ENat.coe_one, edist_eq_one_iff_adj]
  decide

theorem Walk.isPath_of_length_eq_dist (p : G.Walk u v) (hp : p.length = G.dist u v) :
    p.IsPath := by
  classical
  have : p.bypass = p := by
    apply Walk.bypass_eq_self_of_length_le
    calc p.length
      _ = G.dist u v := hp
      _ ≤ p.bypass.length := dist_le p.bypass
  rw [← this]
  apply Walk.bypass_isPath

lemma Reachable.exists_path_of_dist (hr : G.Reachable u v) :
    ∃ (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v := by
  obtain ⟨p, h⟩ := hr.exists_walk_length_eq_dist
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

lemma Connected.exists_path_of_dist (hconn : G.Connected) (u v : V) :
    ∃ (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v := by
  obtain ⟨p, h⟩ := hconn.exists_walk_length_eq_dist  u v
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

@[simp]
lemma dist_bot : (⊥ : SimpleGraph V).dist u v = 0 := by
  by_cases h : u = v <;> simp [h]

lemma dist_top_of_ne (h : u ≠ v) : (⊤ : SimpleGraph V).dist u v = 1 := by
  simp [h]

lemma dist_top [DecidableEq V] : (⊤ : SimpleGraph V).dist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

/-- Supergraphs have smaller or equal distances to their subgraphs. -/
@[gcongr]
protected theorem Reachable.dist_anti {G' : SimpleGraph V} (h : G ≤ G') (hr : G.Reachable u v) :
    G'.dist u v ≤ G.dist u v := by
  obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_dist
  rw [← hw, ← Walk.length_map (Hom.mapSpanningSubgraphs h)]
  apply dist_le

end dist

end SimpleGraph
