/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara, Rida Hamadani, Nelson Spence
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.ENat.Lattice

/-!
# Graph metric

This module defines the `SimpleGraph.eDist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `SimpleGraph.dist`
which is the `ℕ`-valued version of `SimpleGraph.eDist`, and `SimpleGraph.ball` which is the open
ball in the graph extended metric.

## Main definitions

- `SimpleGraph.eDist` is the graph extended metric.
- `SimpleGraph.dist` is the graph metric.
- `SimpleGraph.ball` is the open ball of a given radius around a vertex.

## TODO

- Provide an additional computable version of `SimpleGraph.dist`
  for when `G` is connected.

- When directed graphs exist, a directed notion of distance,
  likely `ENat`-valued.

## Tags

graph metric, distance, ball
-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V)

/-! ## Metric -/

section eDist

/--
The extended distance between two vertices is the length of the shortest walk between them.
It is `⊤` if no such walk exists.
-/
noncomputable def eDist (u v : V) : ℕ∞ :=
  ⨅ w : G.Walk u v, w.length

@[deprecated (since := "2026-11-27")] alias edist := eDist

variable {G} {H : SimpleGraph W} {u v w : V}

theorem eDist_eq_sInf : G.eDist u v = sInf (Set.range fun w : G.Walk u v ↦ (w.length : ℕ∞)) := rfl

@[deprecated (since := "2026-11-27")] alias edist_eq_sInf := eDist_eq_sInf

protected theorem Reachable.exists_walk_length_eq_eDist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.eDist u v :=
  csInf_mem <| Set.range_nonempty_iff_nonempty.mpr hr

@[deprecated (since := "2026-11-27")]
protected alias Reachable.exists_walk_length_eq_edist := Reachable.exists_walk_length_eq_eDist

protected theorem Connected.exists_walk_length_eq_eDist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.eDist u v :=
  (hconn u v).exists_walk_length_eq_eDist

@[deprecated (since := "2026-11-27")]
protected alias Connected.exists_walk_length_eq_edist := Connected.exists_walk_length_eq_eDist

theorem eDist_le (p : G.Walk u v) :
    G.eDist u v ≤ p.length :=
  sInf_le ⟨p, rfl⟩
protected alias Walk.eDist_le := eDist_le

@[deprecated (since := "2026-11-27")] protected alias Walk.edist_le := Walk.eDist_le

@[simp]
theorem eDist_eq_zero_iff : G.eDist u v = 0 ↔ u = v := by
  simp [eDist]

@[deprecated (since := "2026-11-27")] alias edist_eq_zero_iff := eDist_eq_zero_iff

@[simp]
theorem eDist_self : eDist G v v = 0 :=
  eDist_eq_zero_iff.mpr rfl

@[deprecated (since := "2026-11-27")] alias edist_self := eDist_self

theorem eDist_pos_of_ne (hne : u ≠ v) :
    0 < G.eDist u v :=
  pos_iff_ne_zero.mpr <| eDist_eq_zero_iff.ne.mpr hne

@[deprecated (since := "2026-11-27")] alias edist_pos_of_ne := eDist_pos_of_ne

lemma eDist_eq_top_of_not_reachable (h : ¬G.Reachable u v) :
    G.eDist u v = ⊤ := by
  simp [eDist, not_reachable_iff_isEmpty_walk.mp h]

@[deprecated (since := "2026-11-27")]
alias edist_eq_top_of_not_reachable := eDist_eq_top_of_not_reachable

theorem reachable_of_eDist_ne_top (h : G.eDist u v ≠ ⊤) :
    G.Reachable u v :=
  not_not.mp <| eDist_eq_top_of_not_reachable.mt h

@[deprecated (since := "2026-11-27")] alias reachable_of_edist_ne_top := reachable_of_eDist_ne_top

lemma exists_walk_of_eDist_ne_top (h : G.eDist u v ≠ ⊤) :
    ∃ p : G.Walk u v, p.length = G.eDist u v :=
  (reachable_of_eDist_ne_top h).exists_walk_length_eq_eDist

@[deprecated (since := "2026-11-27")]
alias exists_walk_of_edist_ne_top := exists_walk_of_eDist_ne_top

protected theorem eDist_triangle : G.eDist u w ≤ G.eDist u v + G.eDist v w := by
  cases eq_or_ne (G.eDist u v) ⊤ with
  | inl huv => simp [huv]
  | inr huv =>
    cases eq_or_ne (G.eDist v w) ⊤ with
    | inl hvw => simp [hvw]
    | inr hvw =>
      obtain ⟨p, hp⟩ := exists_walk_of_eDist_ne_top huv
      obtain ⟨q, hq⟩ := exists_walk_of_eDist_ne_top hvw
      rw [← hp, ← hq, ← Nat.cast_add, ← Walk.length_append]
      exact eDist_le _

@[deprecated (since := "2026-11-27")] protected alias edist_triangle := SimpleGraph.eDist_triangle

theorem eDist_comm : G.eDist u v = G.eDist v u := by
  rw [eDist_eq_sInf, ← Set.image_univ, ← Set.image_univ_of_surjective Walk.reverse_surjective,
    ← Set.image_comp, Set.image_univ, Function.comp_def]
  simp_rw [Walk.length_reverse, ← eDist_eq_sInf]

@[deprecated (since := "2026-11-27")] alias edist_comm := eDist_comm

lemma exists_walk_of_eDist_eq_coe {k : ℕ} (h : G.eDist u v = k) :
    ∃ p : G.Walk u v, p.length = k :=
  have : G.eDist u v ≠ ⊤ := by rw [h]; exact ENat.natCast_ne_top _
  have ⟨p, hp⟩ := exists_walk_of_eDist_ne_top this
  ⟨p, Nat.cast_injective (hp.trans h)⟩

@[deprecated (since := "2026-11-27")]
alias exists_walk_of_edist_eq_coe := exists_walk_of_eDist_eq_coe

lemma eDist_ne_top_iff_reachable : G.eDist u v ≠ ⊤ ↔ G.Reachable u v := by
  refine ⟨reachable_of_eDist_ne_top, fun h ↦ ?_⟩
  by_contra hx
  simp only [eDist, iInf_eq_top, ENat.natCast_ne_top] at hx
  exact h.elim hx

@[deprecated (since := "2026-11-27")] alias edist_ne_top_iff_reachable := eDist_ne_top_iff_reachable

/--
The extended distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
theorem eDist_eq_one_iff_adj : G.eDist u v = 1 ↔ G.Adj u v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw⟩ := exists_walk_of_eDist_ne_top <| by rw [h]; simp
    exact w.adj_of_length_eq_one <| Nat.cast_eq_one.mp <| h ▸ hw
  · exact le_antisymm (eDist_le h.toWalk) (Order.one_le_iff_pos.mpr <| eDist_pos_of_ne h.ne)

@[deprecated (since := "2026-11-27")] alias edist_eq_one_iff_adj := eDist_eq_one_iff_adj

lemma eDist_le_one_iff_adj_or_eq : G.eDist u v ≤ 1 ↔ G.Adj u v ∨ u = v := by
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, or_false]
    have h : 0 < G.eDist u v := eDist_pos_of_ne huv
    rw [(Order.one_le_iff_pos.mpr h).ge_iff_eq']
    exact eDist_eq_one_iff_adj

@[deprecated (since := "2026-11-27")] alias edist_le_one_iff_adj_or_eq := eDist_le_one_iff_adj_or_eq

lemma eDist_eq_two_iff {u v : V} :
    G.eDist u v = 2 ↔ u ≠ v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ le_antisymm ?_ ?_⟩
  · simp +decide [← G.eDist_eq_zero_iff.not (b := u = v), h]
  · simp +decide [← eDist_eq_one_iff_adj, h]
  · obtain ⟨w, hw⟩ := exists_walk_of_eDist_eq_coe h
    use w.getVert 1
    suffices w.getVert 1 ∈ G.commonNeighbors (w.getVert 0) (w.getVert w.length) by simpa
    refine hw ▸ G.mem_commonNeighbors.mp ?_
    exact ⟨w.adj_getVert_succ (by simp [hw]), (w.adj_getVert_succ (by simp [hw])).symm⟩
  · obtain ⟨w, hw⟩ := h.2.2
    rw [mem_commonNeighbors] at hw
    have := (Walk.cons hw.1 <| .cons hw.2.symm .nil).eDist_le
    simp_all
  · by_contra
    simp_all [Order.le_one_iff]

@[deprecated (since := "2026-11-27")] alias edist_eq_two_iff := eDist_eq_two_iff

lemma two_lt_eDist_iff {u v : V} :
    2 < G.eDist u v ↔ u ≠ v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v) = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ lt_of_le_of_ne ?_ (Ne.symm ?_)⟩
  · have hn : u ≠ v := fun hc ↦ by simp [hc] at h
    have : ¬ G.Adj u v := fun hc ↦ by simp +decide [eDist_eq_one_iff_adj.mpr hc] at h
    use hn, this
    by_contra! hc
    simp [eDist_eq_two_iff.mpr ⟨hn, this, hc⟩] at h
  · rw [← one_add_one_eq_two]
    refine Order.add_one_le_of_lt <| lt_of_le_of_ne ?_ ?_
    <;> grind [Order.one_le_iff_pos, pos_iff_ne_zero, eDist_eq_zero_iff, eDist_eq_one_iff_adj]
  · simp_all [eDist_eq_two_iff]

@[deprecated (since := "2026-11-27")] alias two_lt_edist_iff := two_lt_eDist_iff

lemma eDist_bot_of_ne (h : u ≠ v) : (⊥ : SimpleGraph V).eDist u v = ⊤ := by
  rwa [ne_eq, ← reachable_bot.not, ← eDist_ne_top_iff_reachable.not, not_not] at h

@[deprecated (since := "2026-11-27")] alias edist_bot_of_ne := eDist_bot_of_ne

lemma eDist_bot [DecidableEq V] : (⊥ : SimpleGraph V).eDist u v = (if u = v then 0 else ⊤) := by
  by_cases h : u = v <;> simp [h, eDist_bot_of_ne]

@[deprecated (since := "2026-11-27")] alias edist_bot := eDist_bot

lemma eDist_top_of_ne (h : u ≠ v) : (⊤ : SimpleGraph V).eDist u v = 1 := by
  simp [h]

@[deprecated (since := "2026-11-27")] alias edist_top_of_ne := eDist_top_of_ne

lemma eDist_top [DecidableEq V] : (⊤ : SimpleGraph V).eDist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

@[deprecated (since := "2026-11-27")] alias edist_top := eDist_top

theorem Hom.eDist_le (f : G →g H) (u v : V) : H.eDist (f u) (f v) ≤ G.eDist u v := by
  refine le_iInf fun p ↦ ?_
  simpa using (p.map f).eDist_le

@[deprecated (since := "2026-11-27")] alias Hom.edist_le := Hom.eDist_le

@[simp]
theorem Iso.eDist_eq (f : G ≃g H) (u v : V) : H.eDist (f u) (f v) = G.eDist u v := by
  apply le_antisymm (f.toHom.eDist_le u v)
  simpa using f.symm.toHom.eDist_le (f u) (f v)

@[deprecated (since := "2026-11-27")] alias Iso.edist_eq := Iso.eDist_eq

/-- Supergraphs have smaller or equal extended distances to their subgraphs. -/
@[gcongr]
theorem eDist_anti {G' : SimpleGraph V} (h : G ≤ G') :
    G'.eDist u v ≤ G.eDist u v :=
  (Hom.ofLE h).eDist_le u v

@[deprecated (since := "2026-11-27")] alias edist_anti := eDist_anti

end eDist

section dist

/--
The distance between two vertices is the length of the shortest walk between them.
If no such walk exists, this uses the junk value of `0`.
-/
noncomputable def dist (u v : V) : ℕ :=
  (G.eDist u v).toNat

variable {G} {H : SimpleGraph W} {u v w : V}

theorem dist_eq_sInf : G.dist u v = sInf (Set.range (Walk.length : G.Walk u v → ℕ)) :=
  ENat.iInf_toNat

@[grind =]
lemma Reachable.coe_dist_eq_eDist (h : G.Reachable u v) : G.dist u v = G.eDist u v :=
  ENat.natCast_toNat <| eDist_ne_top_iff_reachable.mpr h

@[deprecated (since := "2026-11-27")]
alias Reachable.coe_dist_eq_edist := Reachable.coe_dist_eq_eDist

protected theorem Reachable.exists_walk_length_eq_dist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)

protected theorem Connected.exists_walk_length_eq_dist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ (hconn u v).exists_walk_length_eq_dist

theorem dist_le (p : G.Walk u v) : G.dist u v ≤ p.length :=
  dist_eq_sInf ▸ Nat.sInf_le ⟨p, rfl⟩

theorem natCast_dist_le_eDist : G.dist u v ≤ G.eDist u v :=
  ENat.natCast_toNat_le_self _

@[deprecated (since := "2026-11-27")] alias natCast_dist_le_edist := natCast_dist_le_eDist

@[simp]
theorem dist_eq_zero_iff_eq_or_not_reachable :
    G.dist u v = 0 ↔ u = v ∨ ¬G.Reachable u v := by simp [dist_eq_sInf, Nat.sInf_eq_zero, Reachable]

@[simp, grind =]
theorem dist_self : dist G v v = 0 := by simp

protected theorem Reachable.dist_eq_zero_iff (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by simp [hr]

protected theorem Reachable.pos_dist_of_ne (h : G.Reachable u v) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by simp [h, hne])

protected theorem Reachable.one_lt_dist_of_ne_of_not_adj (h : G.Reachable u v) (hne : u ≠ v)
    (hnadj : ¬G.Adj u v) : 1 < G.dist u v :=
  Nat.lt_of_le_of_ne (h.pos_dist_of_ne hne) (by
    by_contra hc
    obtain ⟨p, hp⟩ := Reachable.exists_walk_length_eq_dist h
    exact hnadj (Walk.exists_length_eq_one_iff.mp ⟨p, hc ▸ hp⟩))

protected theorem Connected.dist_eq_zero_iff (hconn : G.Connected) :
    G.dist u v = 0 ↔ u = v := by simp [hconn u v]

protected theorem Connected.pos_dist_of_ne (hconn : G.Connected) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero fun h ↦ False.elim <| hne <| (hconn.dist_eq_zero_iff).mp h

protected theorem Connected.one_lt_dist_of_ne_of_not_adj (h : G.Connected) (hne : u ≠ v)
    (hnadj : ¬G.Adj u v) : 1 < G.dist u v :=
  Reachable.one_lt_dist_of_ne_of_not_adj (h u v) hne hnadj

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

lemma Reachable.dist_triangle_left (h : G.Reachable u v) (w) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast, ENat.natCast_add]
  grind [SimpleGraph.eDist_triangle, Reachable.trans, Reachable.symm]

lemma Reachable.dist_triangle_right (h : G.Reachable v w) (u) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast, ENat.natCast_add]
  grind [SimpleGraph.eDist_triangle, Reachable.trans, Reachable.symm]

theorem dist_comm : G.dist u v = G.dist v u := by
  rw [dist, dist, eDist_comm]

lemma dist_ne_zero_iff_ne_and_reachable : G.dist u v ≠ 0 ↔ u ≠ v ∧ G.Reachable u v := by
  simp

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
  rw [dist, ENat.toNat_eq_iff, ENat.natCast_one, eDist_eq_one_iff_adj]
  decide

theorem Adj.diff_dist_adj (hadj : G.Adj v w) :
    G.dist u w = G.dist u v ∨ G.dist u w = G.dist u v + 1 ∨ G.dist u w = G.dist u v - 1 := by
  by_cases! huw : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable, Reachable.trans, Adj.reachable]
  have : G.dist v w = 1 := dist_eq_one_iff_adj.mpr hadj
  have : G.dist w v = 1 := dist_eq_one_iff_adj.mpr hadj.symm
  have : G.dist u w ≤ G.dist u v + G.dist v w := hadj.reachable.dist_triangle_right u
  have : G.dist u v ≤ G.dist u w + G.dist w v := huw.dist_triangle_left v
  lia

theorem Walk.isPath_of_length_eq_dist (p : G.Walk u v) (hp : p.length = G.dist u v) :
    p.IsPath := by
  classical
  have : p.bypass = p := by
    rw [← length_le_bypass_length_iff]
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
  obtain ⟨p, h⟩ := hconn.exists_walk_length_eq_dist u v
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

@[simp]
lemma dist_bot : (⊥ : SimpleGraph V).dist u v = 0 := by
  by_cases h : u = v <;> simp [h]

lemma dist_top_of_ne (h : u ≠ v) : (⊤ : SimpleGraph V).dist u v = 1 := by
  simp [h]

lemma dist_top [DecidableEq V] : (⊤ : SimpleGraph V).dist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

lemma length_eq_dist_of_subwalk {u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h₁ : p₁.length = G.dist u v) (h₂ : p₂.IsSubwalk p₁) : p₂.length = G.dist u' v' := by
  refine (dist_le _).eq_of_not_lt' fun hh ↦ ?_
  obtain ⟨ru, rv, h⟩ := h₂
  obtain ⟨s, _⟩ := p₂.reachable.exists_path_of_dist
  let r := ru.append s |>.append rv
  have : p₁.length = ru.length + p₂.length + rv.length := by simp [h]
  have : r.length = ru.length + s.length + rv.length := by simp [r]
  have := dist_le r
  lia

theorem Hom.dist_le (f : G →g H) (hr : G.Reachable u v) : H.dist (f u) (f v) ≤ G.dist u v :=
  ENat.toNat_le_toNat (f.eDist_le u v) (eDist_ne_top_iff_reachable.mpr hr)

@[simp]
theorem Iso.dist_eq (f : G ≃g H) (u v : V) : H.dist (f u) (f v) = G.dist u v :=
  congr($(f.eDist_eq u v).toNat)

/-- Supergraphs have smaller or equal distances to their subgraphs. -/
@[gcongr]
protected theorem Reachable.dist_anti {G' : SimpleGraph V} (h : G ≤ G') (hr : G.Reachable u v) :
    G'.dist u v ≤ G.dist u v :=
  (Hom.ofLE h).dist_le hr

/-- This bundles and abstracts some facts about the first three vertices of a shortest walk
of length at least two: the first and third nodes are different and not connected. -/
lemma Walk.exists_adj_adj_not_adj_ne {p : G.Walk v w} (hp : p.length = G.dist v w)
    (hl : 1 < G.dist v w) : ∃ (x a b : V), G.Adj x a ∧ G.Adj a b ∧ ¬ G.Adj x b ∧ x ≠ b := by
  use v, p.getVert 1, p.getVert 2
  have hnp : ¬p.Nil := by grind [Nil.length_eq_zero]
  have : p.tail.tail.length < p.tail.length := by
    rw [← p.tail.length_tail_add_one (by
      simp only [not_nil_iff_lt_length, ← p.length_tail_add_one hnp] at hp ⊢
      lia)]
    lia
  have : p.tail.length < p.length := by rw [← p.length_tail_add_one hnp]; lia
  by_cases hv : v = p.getVert 2
  · have : G.dist v w ≤ p.tail.tail.length := by
      simpa [hv, p.getVert_tail] using dist_le p.tail.tail
    lia
  by_cases hadj : G.Adj v (p.getVert 2)
  · have : G.dist v w ≤ p.tail.tail.length + 1 :=
      dist_le <| p.tail.tail.cons <| p.getVert_tail ▸ hadj
    lia
  exact ⟨p.adj_snd hnp, p.adj_getVert_succ (hp ▸ hl), hadj, hv⟩

end dist

/-! ## Ball -/

section ball

/-- The open ball of radius `r` centered at the vertex `c` in the graph extended metric. -/
def ball (c : V) (r : ℕ∞) : Set V :=
  {v | G.eDist v c < r}

variable {G} {c v : V} {r r₁ r₂ : ℕ∞}

@[simp]
theorem mem_ball : v ∈ G.ball c r ↔ G.eDist v c < r := .rfl

/-- The ball of radius zero is empty. -/
@[simp]
theorem ball_zero : G.ball c 0 = ∅ := by simp [ball]

/-- The ball of radius one consists of just the center. -/
@[simp]
theorem ball_one : G.ball c 1 = {c} := by
  simp [ball]

/-- The ball of radius two consists of the center and its neighbors. -/
@[simp]
theorem ball_two : G.ball c 2 = insert c (G.neighborSet c) := by
  ext v
  simp [one_add_one_eq_two.symm, ENat.lt_add_one_iff ENat.one_ne_top,
    eDist_le_one_iff_adj_or_eq, adj_comm, or_comm]

/-- The ball of radius `⊤` is the connected component of the center. -/
theorem ball_top :
    G.ball c ⊤ = (G.connectedComponentMk c).supp := by
  simp [Set.ext_iff, lt_top_iff_ne_top, eDist_ne_top_iff_reachable]

/-- A vertex is in the ball of radius `⊤` iff it is reachable from the center. -/
theorem mem_ball_top : v ∈ G.ball c ⊤ ↔ G.Reachable v c := by
  simp [lt_top_iff_ne_top, eDist_ne_top_iff_reachable]

/-- Balls are monotone in the radius. -/
@[gcongr]
theorem ball_mono (h : r₁ ≤ r₂) : G.ball c r₁ ⊆ G.ball c r₂ :=
  fun _ hv ↦ lt_of_lt_of_le hv h

/-- The center vertex belongs to any ball of positive radius. -/
theorem mem_ball_self (hr : 0 < r) : c ∈ G.ball c r := by
  simp [ball, hr]

/-- Ball membership is symmetric in center and point. -/
theorem mem_ball_comm : v ∈ G.ball c r ↔ c ∈ G.ball v r := by
  simp [ball, eDist_comm]

end ball

end SimpleGraph
