/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Duplicate
public import Mathlib.Data.List.NodupEquivFin

/-!
# Simple quiver paths and cycles

Parallel to `SimpleGraph.Walk` in `Mathlib/Combinatorics/SimpleGraph/Paths.lean`:

| `SimpleGraph.Walk` | `Quiver.Path` |
|--------------------|---------------|
| `support.Nodup` | `IsPath` (`vertices.Nodup`) |
| `support.tail.Nodup` on a loop | `IsSimple` (`vertices.dropLast.Nodup`) |
| `IsCycle` | `IsCycle` (`0 < length ∧ IsSimple`) |

`IsSimple` allows the endpoint to repeat the start (simple directed cycle). `IsPath` forbids
any repeated vertex and is strictly stronger.

Acyclicity is `Quiver.IsAcyclic` in `ConnectedComponent.lean` (no nontrivial closed paths),
equivalent to forbidding `IsCycle` loops.

`Quiver.cycleLengths` ([PR #39913](https://github.com/leanprover-community/mathlib4/pull/39913))
records lengths of positive loops without a simplicity hypothesis.

For cardinality bounds use `p.vertices.toFinset` (see `List.toFinset_card_of_nodup`).
-/

@[expose] public section

namespace Quiver.Path

open List

variable {V : Type*} [Quiver V]

/-- A path with no repeated vertices (cf. `SimpleGraph.Walk.IsPath`). -/
@[reducible] def IsPath {a b : V} (p : Path a b) : Prop :=
  p.vertices.Nodup

/-- A path with no repeated vertices except possibly at the end. -/
@[reducible] def IsSimple {a b : V} (p : Path a b) : Prop :=
  p.vertices.dropLast.Nodup

/-- A nontrivial simple closed walk. -/
def IsCycle {a : V} (p : Path a a) : Prop :=
  0 < p.length ∧ p.IsSimple

@[simp] lemma isPath_nil {a : V} : IsPath (nil : Path a a) := by simp [IsPath]

@[simp] lemma isPath_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    IsPath (p.cons e) ↔ IsPath p ∧ c ∉ p.vertices := by
  simp only [IsPath, vertices_cons]
  rw [nodup_concat]; aesop

@[simp] lemma isSimple_of_isPath {a b : V} {p : Path a b} (h : IsPath p) : IsSimple p :=
  h.sublist (dropLast_sublist (l := p.vertices))

lemma not_isPath_of_not_isSimple {a b : V} {p : Path a b} (h : ¬IsSimple p) : ¬IsPath p := by
  intro hp; exact h (isSimple_of_isPath hp)

lemma count_vertices_ge_two_of_duplicate_dropLast [DecidableEq V] {a : V} {s : Path a a}
    {v : V} (hv : Duplicate v s.vertices.dropLast) : 2 ≤ s.vertices.count v := by
  have h_drop : 2 ≤ (s.vertices.dropLast).count v := (duplicate_iff_two_le_count).1 hv
  rw [← dropLast_append_end_eq s, count_append, count_singleton]
  exact Nat.le_trans h_drop (by split_ifs <;> omega)

/-! ### Splitting at a repeated vertex -/

lemma mem_dropLast_of_comp_count_ge_two [DecidableEq V] {a v : V} {s : Path a a}
    {p₁ : Path a v} {p₂ : Path v a} (hp : s = p₁.comp p₂) (hv_ge₂ : 2 ≤ s.vertices.count v)
    (hv_not_tail : v ∉ p₂.vertices.tail) : v ∈ p₁.vertices.dropLast := by
  have h_p2_count : p₂.vertices.count v = 1 := by
    cases hv : p₂.vertices with
    | nil => exact (vertices_ne_nil p₂ hv).elim
    | cons hd tl =>
      have h_eq : hd = v := Option.some_inj.mp (by simpa [hv] using vertices_head? p₂)
      rw [h_eq] at hv ⊢
      have h_tl : v ∉ tl := fun h_in => hv_not_tail (by rw [hv]; exact h_in)
      simp [count_cons_self, count_eq_zero.mpr h_tl]
  have h2 : 2 ≤ (p₁.vertices.dropLast ++ p₂.vertices).count v := by
    simpa [← vertices_comp, hp] using hv_ge₂
  rw [count_append, h_p2_count] at h2
  exact count_pos_iff.mp (by omega)

lemma repeated_vertex_in_prefix_dropLast [DecidableEq V] {a : V} (s : Path a a)
    (h_not_simple : ¬IsSimple s) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v a),
      v ∈ p₁.vertices.dropLast ∧ s = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
  dsimp [IsSimple] at h_not_simple
  obtain ⟨v, hv_dup⟩ := exists_duplicate_iff_not_nodup.mpr h_not_simple
  have hv_in : v ∈ s.vertices := mem_of_mem_dropLast (Duplicate.mem hv_dup)
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ := exists_eq_comp_and_notMem_tail_of_mem_vertices s hv_in
  have hv_in_p1 := mem_dropLast_of_comp_count_ge_two hp
    (count_vertices_ge_two_of_duplicate_dropLast hv_dup) hv_not_tail
  exact ⟨v, p₁, p₂, hv_in_p1, hp, hv_not_tail⟩

lemma extract_cycle_from_prefix [DecidableEq V] {a vertex : V} {p₁ : Path a vertex}
    (h_in_drop : vertex ∈ p₁.vertices.dropLast) :
    ∃ (q : Path a vertex) (c : Path vertex vertex),
      p₁ = q.comp c ∧ vertex ∉ q.vertices.dropLast := by
  let i := p₁.vertices.idxOf vertex
  have h_mem := mem_of_mem_dropLast h_in_drop
  obtain ⟨_v, q, c, h_comp, _h_len, h_v⟩ :=
    p₁.exists_eq_comp_and_length_eq_of_lt_length i (idxOf_lt_length_of_mem h_mem)
  rcases h_v.trans (getElem_idxOf (idxOf_lt_length_of_mem h_mem)) with rfl
  refine ⟨q, c, h_comp, fun h => ?_⟩
  have h_pre : q.vertices.dropLast <+: p₁.vertices := by rw [h_comp, vertices_comp]; grind
  have h_idx := (IsPrefix.idxOf_eq_of_mem h_pre h).symm
  have h_lt := idxOf_lt_length_of_mem h
  rw [← h_idx, length_dropLast, vertices_length] at h_lt
  grind

lemma extracted_cycle_has_positive_length {a v : V} {p₁ q : Path a v} {c : Path v v}
    (h_p1_split : p₁ = q.comp c) (hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast)
    (hv_not_in_q : v ∉ q.vertices.dropLast) : c.length > 0 := by
  by_cases h_len_zero : c.length = 0
  · have hc_nil : c = Path.nil := (length_eq_zero_iff c).mp h_len_zero
    have h_p1_eq_q : p₁ = q := by rw [h_p1_split, hc_nil, comp_nil]
    exact hv_not_in_q (h_p1_eq_q ▸ hv_in_p1_dropLast) |> False.elim
  · exact Nat.pos_of_ne_zero h_len_zero

lemma removing_cycle_gives_shorter_path {a v : V} {s : Path a a} {q : Path a v} {c : Path v v}
    {p₂ : Path v a} (hp : s = (q.comp c).comp p₂) (hc_pos : c.length > 0) :
    (q.comp p₂).length < s.length := by
  rw [hp, comp_assoc]
  simp only [length_comp]
  grind

/-- When `c = c_cycle` and the outer peel is `nil.comp nil`, extract a shorter positive loop. -/
lemma exists_shorter_pos_loop_of_nil_nil_comp [DecidableEq V] {a : V} {c c_cycle : Path a a}
    (hc_eq : c = c_cycle) (hc_pos : 0 < c.length)
    (hc_min : ∀ p' : Path a a, p'.length > 0 → c.length ≤ p'.length) (h_not_simple : ¬IsSimple c_cycle) :
    ∃ p : Path a a, 0 < p.length ∧ p.length < c.length := by
  classical
  dsimp [IsSimple] at h_not_simple
  obtain ⟨x, hx_dup⟩ := exists_duplicate_iff_not_nodup.mpr h_not_simple
  have hx_count := (duplicate_iff_two_le_count).1 hx_dup
  by_cases hx : x = a
  · obtain ⟨n, m, hnm, hn, hm⟩ :=
      (duplicate_iff_exists_distinct_get (l := c_cycle.vertices.dropLast)).1 hx_dup
    let i : ℕ := if n.val = 0 then m.val else n.val
    have hi_pos : 0 < i := by
      dsimp [i]; split_ifs with hn0
      · simpa [hn0] using Fin.lt_def.mp hnm
      · exact Nat.pos_of_ne_zero hn0
    have hi_lt_drop : i < c_cycle.vertices.dropLast.length := by
      dsimp [i]; split_ifs with hn0
      · simpa [hn0] using Fin.is_lt m
      · simpa using Fin.is_lt n
    have hi_lt : i < c_cycle.vertices.length := by
      rw [← dropLast_append_end_eq c_cycle, length_append, length_singleton]
      exact lt_trans hi_lt_drop (Nat.lt_succ_self _)
    have hi_get_drop : c_cycle.vertices.dropLast[i]'hi_lt_drop = x := by
      dsimp [i]; split_ifs with hn0
      · simpa [hn0, get_eq_getElem] using hm.symm
      · simpa [get_eq_getElem] using hn.symm
    have hi_get : c_cycle.vertices[i]'hi_lt = x :=
      by simpa [dropLast_append_end_eq, getElem_append_left hi_lt_drop] using hi_get_drop
    obtain ⟨w, p_short, _, _, h_len, hw⟩ :=
      c_cycle.exists_eq_comp_and_length_eq_of_lt_length i hi_lt
    have ha_eq : w = a := hw.trans (hx ▸ hi_get)
    subst ha_eq
    refine ⟨p_short, ?_, ?_⟩
    · rw [h_len]; exact hi_pos
    · rw [h_len, hc_eq]; simpa [vertices_length, length_dropLast] using hi_lt_drop
  · obtain ⟨p₁x, p₂x, hcompx, hx_not_tail⟩ :=
      c_cycle.exists_eq_comp_and_notMem_tail_of_mem_vertices (mem_of_mem_dropLast (Duplicate.mem hx_dup))
    have hx_in_p1 := mem_dropLast_of_comp_count_ge_two hcompx
      (count_vertices_ge_two_of_duplicate_dropLast hx_dup) hx_not_tail
    obtain ⟨q_x, c_x, hsplit1, hx_not⟩ := extract_cycle_from_prefix (p₁ := p₁x) hx_in_p1
    have hc_x_pos := extracted_cycle_has_positive_length hsplit1 hx_in_p1 hx_not
    have hcomp' : c_cycle = (q_x.comp c_x).comp p₂x := by rw [hcompx, hsplit1, comp_assoc]
    have h_shorter : (q_x.comp p₂x).length < c.length := by rw [hc_eq]; exact removing_cycle_gives_shorter_path hcomp' hc_x_pos
    refine ⟨(q_x.comp p₂x), ?_, h_shorter⟩
    by_contra hzero
    have hlen' : q_x.length + p₂x.length = 0 := by
      rw [← length_comp, Nat.eq_zero_of_le_zero (le_of_not_gt hzero)]
    rcases Nat.add_eq_zero_iff.mp hlen' with ⟨hq, hp₂⟩
    cases q_x with
    | nil =>
      cases p₂x with
      | nil => exact absurd rfl hx
      | cons _ _ => simp [length_cons] at hlen'
    | cons _ _ => simp [length_cons] at hlen'

lemma exists_shorter_pos_loop_of_not_isSimple [DecidableEq V] {a : V} {c : Path a a}
    (hc_pos : 0 < c.length) (hc_min : ∀ p' : Path a a, p'.length > 0 → c.length ≤ p'.length)
    (h_not_simple : ¬IsSimple c) :
    ∃ p : Path a a, 0 < p.length ∧ p.length < c.length := by
  classical
  obtain ⟨v, p₁, p₂, hv_in_drop, hp_split, _⟩ :=
    repeated_vertex_in_prefix_dropLast c h_not_simple
  obtain ⟨q, c_cycle, hp₁_split, hv_not_in_q⟩ := extract_cycle_from_prefix hv_in_drop
  have hc_cycle_pos := extracted_cycle_has_positive_length hp₁_split hv_in_drop hv_not_in_q
  have hp_comp : c = (q.comp c_cycle).comp p₂ := by rw [hp_split, hp₁_split, comp_assoc]
  have h_shorter : (q.comp p₂).length < c.length :=
    removing_cycle_gives_shorter_path hp_comp hc_cycle_pos
  by_cases hq_pos : (q.comp p₂).length > 0
  · exact ⟨q.comp p₂, hq_pos, h_shorter⟩
  · have hlen : q.length + p₂.length = 0 := by
      rw [← length_comp, Nat.eq_zero_of_le_zero (le_of_not_gt hq_pos)]
    rcases Nat.add_eq_zero_iff.mp hlen with ⟨hq, hp₂⟩
    cases q with
    | nil =>
      cases p₂ with
      | nil =>
        obtain ⟨p, hp_pos, hp_lt⟩ :=
          exists_shorter_pos_loop_of_nil_nil_comp (by simpa [comp_nil] using hp_comp) hc_pos hc_min
            (by simpa [hp_comp] using h_not_simple)
        exact ⟨p, hp_pos, hp_lt⟩
      | cons _ _ => simp [length_cons] at hlen
    | cons _ _ => simp [length_cons] at hlen

/-- A shortest positive loop is simple. -/
theorem shortest_positive_loop_is_simple [DecidableEq V] {a : V} {c : Path a a}
    (hc_pos : 0 < c.length) (hc_min : ∀ p' : Path a a, p'.length > 0 → c.length ≤ p'.length) :
    c.IsSimple := by
  by_contra h
  obtain ⟨p, hp_pos, hp_lt⟩ := exists_shorter_pos_loop_of_not_isSimple hc_pos hc_min h
  exact lt_irrefl _ ((hc_min p hp_pos).trans_lt hp_lt)

end Quiver.Path
