/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Quiver.Path--.Decomposition
import Mathlib.Data.Set.Insert
import Mathlib.Data.List.Basic

/-!
# Path Vertices

This file provides lemmas for reasoning about the vertices of a path.
-/

namespace Quiver.Path

open List

variable {V : Type*} [Quiver V]

/-- The end vertex of a path. A path `p : Path a b` has `p.end = b`. -/
def «end» {a : V} : ∀ {b : V}, Path a b → V
  | b, _ => b

@[simp]
lemma end_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : (p.cons e).end = c := rfl

/-- The list of vertices in a path, including the start and end vertices. -/
def vertices {a : V} : ∀ {b : V}, Path a b → List V
  | _, nil => [a]
  | _, cons p e => (p.vertices).concat (p.cons e).end

@[simp]
lemma vertices_nil (a : V) : (nil : Path a a).vertices = [a] := rfl

@[simp]
lemma vertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  (p.cons e).vertices = p.vertices.concat c := rfl

/-- The vertex list of `cons` — convenient `simp` form. -/
lemma mem_vertices_cons {a b c : V} (p : Path a b)
    (e : b ⟶ c) {x : V} :
    x ∈ (p.cons e).vertices ↔ x ∈ p.vertices ∨ x = c := by
  simp only [vertices_cons]
  simp_all only [concat_eq_append, mem_append, mem_cons, not_mem_nil, or_false]

lemma verticesSet_nil {a : V} : {v | v ∈ (nil : Path a a).vertices} = {a} := by
  simp only [vertices_nil, mem_singleton, Set.ext_iff, Set.mem_singleton_iff]
  exact fun x ↦ Set.mem_setOf

/-- The length of vertices list equals path length plus one -/
@[simp]
lemma vertices_length {V : Type*} [Quiver V] {a b : V} (p : Path a b) :
    p.vertices.length = p.length + 1 := by
  induction p with
  | nil => simp
  | cons p' e ih =>
    simp [vertices_cons, length_cons, ih]

lemma length_vertices_pos {a b : V} (p : Path a b) :
    0 < p.vertices.length := by simp

lemma vertices_ne_nil {a : V} {b : V} (p : Path a b) : p.vertices ≠ [] := by
  simp [← length_pos_iff_ne_nil]

/-- The head of the vertices list is the start vertex -/
@[simp]
lemma vertices_head? {a b : V} (p : Path a b) : p.vertices.head? = some a := by
  induction p with
  | nil => simp only [vertices_nil, head?_cons]
  | cons p' e ih => simp [ih]

@[simp]
lemma getElem_vertices_zero {a b : V} (p : Path a b) : p.vertices[0] = a := by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

@[simp]
lemma vertices_getLast {a b : V} (p : Path a b) (h : p.vertices ≠ [] := p.vertices_ne_nil) :
    p.vertices.getLast h = b := by
  induction p with
  | nil => simp only [vertices_nil, getLast_singleton]
  | cons p' e ih => simp

@[simp]
lemma vertices_comp {a b c : V} (p : Path a b) (q : Path b c) :
  (p.comp q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction q with
  | nil => simpa using (dropLast_append_getLast p.vertices_ne_nil).symm
  | cons q' e ih => simp [ih]

lemma start_mem_vertices {a b : V} (p : Path a b) : a ∈ p.vertices := by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

@[simp] lemma length_eq_zero_iff {a : V} (p : Path a a) :
    p.length = 0 ↔ p = Path.nil := by
  cases p <;> tauto

/-- The head of the vertices list is the start vertex. -/
@[simp]
lemma vertices_head_eq {a b : V} (p : Path a b) (h : p.vertices ≠ [] := p.vertices_ne_nil) :
    p.vertices.head h = a := by
  induction p with
  | nil => simp only [vertices_nil, head_cons]
  | cons p' _ ih => simp [head_append_of_ne_nil (vertices_ne_nil p'), ih]

/-- The last element of the vertices list is the end vertex. -/
lemma vertices_getLast_eq {a b : V} (p : Path a b) (h : p.vertices ≠ [] := p.vertices_ne_nil) :
  p.vertices.getLast h = b := by
  exact vertices_getLast p (vertices_ne_nil p)

lemma vertices_comp_get_length_eq {a b c : V} (p₁ : Path a c) (p₂ : Path c b)
    (h : p₁.length < (p₁.comp p₂).vertices.length := by simp) :
    (p₁.comp p₂).vertices.get ⟨p₁.length, h⟩ = c := by
  simp

@[simp]
lemma vertices_toPath {i j : V} (e : i ⟶ j) :
    (e.toPath).vertices = [i, j] := by
  change (Path.nil.cons e).vertices = [i, j]
  simp

lemma vertices_toPath_tail {i j : V} (e : i ⟶ j) :
    (e.toPath).vertices.tail = [j] := by
  simp

/-- If a composition is `nil`, the left component must be `nil`
    (proved via lengths, avoiding dependent pattern-matching). -/
lemma nil_of_comp_eq_nil_left {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = Path.nil) : p.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_right this

/-- If a composition is `nil`, the right component must be `nil` -/
lemma nil_of_comp_eq_nil_right {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = Path.nil) : q.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_left this

lemma comp_eq_nil_iff {a b : V} {p : Path a b} {q : Path b a} :
    p.comp q = Path.nil ↔ p.length = 0 ∧ q.length = 0 := by
  refine ⟨fun h ↦ ⟨nil_of_comp_eq_nil_left h, nil_of_comp_eq_nil_right h⟩, fun ⟨hp, hq⟩ ↦ ?_⟩
  induction p with
  | nil => simpa using (length_eq_zero_iff q).mp hq
  | cons p' _ ihp => simp at hp

@[simp]
lemma end_mem_vertices {a b : V} (p : Path a b) : b ∈ p.vertices := by
  have h₁ : p.vertices.getLast (vertices_ne_nil p) = b :=
    vertices_getLast p (vertices_ne_nil p)
  have h₂ := getLast_mem (l := p.vertices) (vertices_ne_nil p)
  simpa [h₁] using h₂

/-!  ### Path vertices decomposition -/

section

variable {V : Type*} [Quiver V]

open List

/-- Given a path `p : Path a b` and an index `n ≤ p.length`,
    we can split `p = p₁.comp p₂` with `p₁.length = n`. -/
theorem exists_comp_of_length_le {a b : V} (p : Path a b) {n : ℕ} (hn : n ≤ p.length) :
    ∃ (c : V) (p₁ : Path a c) (p₂ : Path c b),
      p = p₁.comp p₂ ∧ p₁.length = n := by
  induction p generalizing n with
  | nil =>
      have h : n = 0 := by simp_all only [length_nil, nonpos_iff_eq_zero]
      subst h
      exact ⟨a, Path.nil, Path.nil, by simp only [comp_nil], rfl⟩
  | cons p' e ih =>
      rename_i c
      rw [length_cons] at hn
      rcases (Nat.le_succ_iff).1 hn with h | h
      · rcases ih h with ⟨d, p₁, p₂, hp, hl⟩
        refine ⟨d, p₁, p₂.cons e, ?_, hl⟩
        simp; rw [hp]
      · subst h
        refine ⟨c, p'.cons e, Path.nil, ?_, ?_⟩
        all_goals simp

/-- If a vertex `v` occurs in the list of vertices of a path `p : Path a b`, then `p` can be
decomposed as a concatenation of a subpath from `a` to `v` and a subpath from `v` to `b`. -/
theorem exists_comp_of_mem_vertices {a b v : V} (p : Path a b)
  (h : v ∈ p.vertices) : ∃ (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ := by
  obtain ⟨l₁, l₂, hv⟩ := exists_mem_split h
  have h_len : l₁.length ≤ p.length := by
    have : p.vertices.length = p.length + 1 := vertices_length p
    have : l₁.length < p.vertices.length := by
      rw [hv, length_append]
      simp
    omega
  obtain ⟨c, p₁, p₂, hp, hl⟩ := exists_comp_of_length_le p h_len
  suffices hvc : v = c by
    subst hvc
    exact ⟨p₁, p₂, hp⟩
  have h_verts : p.vertices = p₁.vertices.dropLast ++ p₂.vertices := by
    rw [hp, vertices_comp]
  have h_l1_len : l₁.length = p₁.vertices.dropLast.length := by aesop
  have h_l1_eq : l₁ = p₁.vertices.dropLast := by
    have : l₁ ++ v :: l₂ = p₁.vertices.dropLast ++ p₂.vertices := by
      rw [← hv, h_verts]
    exact append_inj_left this h_l1_len
  have h_v_l2 : v :: l₂ = p₂.vertices := by
    have : l₁ ++ v :: l₂ = p₁.vertices.dropLast ++ p₂.vertices := by
      rw [← hv, h_verts]
    rw [h_l1_eq] at this
    exact append_cancel_left this
  have : p₂.vertices.head? = some c := by
    cases p₂ with
    | nil => simp only [vertices_nil, head?_cons]
    | cons _ _ => exact vertices_head? _
  rw [← h_v_l2] at this
  simp [head?_cons, Option.some.injEq] at this
  exact this

lemma vertices_head_eq_start {a b : V} (p : Path a b) :
    p.vertices.head (vertices_ne_nil p) = a := by
  induction p with
  | nil => simp only [vertices_nil, head_cons]
  | cons p' _ ih =>
    simp [vertices_cons, concat_eq_append]
    have : p'.vertices ≠ [] := vertices_ne_nil p'
    simp [head_append_of_ne_nil this]

lemma vertices_getLast_eq_end {a b : V} (p : Path a b) :
  p.vertices.getLast (vertices_ne_nil p) = b := by simp

lemma end_eq_vertices_get_of_comp_length {a b c : V} (p₁ : Path a c) (p₂ : Path c b) :
    c = (p₁.comp p₂).vertices.get ⟨p₁.length, by simp⟩ := by simp

/-- `split_at_vertex` decomposes a path `p` at the vertex sitting in
    position `i` of its `vertices` -/
theorem split_at_vertices_index {a b : V} (p : Path a b) (i : ℕ)
    (hi : i < p.vertices.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧
      p₁.length = i ∧
      v = p.vertices.get ⟨i, hi⟩ := by
  have hi_le_len : i ≤ p.length := by
    rw [vertices_length] at hi
    exact Nat.le_of_lt_succ hi
  obtain ⟨v, p₁, p₂, hp, hlen⟩ := exists_comp_of_length_le p hi_le_len
  subst hp
  refine ⟨v, p₁, p₂, rfl, hlen, ?_⟩
  simp [hlen]

lemma not_mem_vertices_dropLast_of_split_at_vertex
    [DecidableEq V] {a b v : V} {p : Path a b}
    (h_v_in_p : v ∈ p.vertices) :
    let i  := p.vertices.idxOf v
    let hi := List.idxOf_lt_length_iff.2 h_v_in_p
    ∀ (c : V) (p_prefix : Path a c) (p_suffix : Path c b)
      (_ : p = p_prefix.comp p_suffix)
      (_ : p_prefix.length = i)
      (_ : c = p.vertices.get ⟨i, hi⟩),
      v ∉ p_prefix.vertices.dropLast := by
  intro i hi c p_prefix p_suffix h_comp h_len_prefix h_c_eq
  subst h_c_eq
  by_contra h_in_prefix
  have h_idx_lt : idxOf v p_prefix.vertices.dropLast < i := by
    have : idxOf v p_prefix.vertices.dropLast <
        p_prefix.vertices.dropLast.length :=
      List.idxOf_lt_length_iff.2 h_in_prefix
    simpa [h_len_prefix, vertices_length,
           length_dropLast] using this
  have h_prefix_in_p : IsPrefix p_prefix.vertices.dropLast p.vertices := by
    have hverts :
        p.vertices = p_prefix.vertices.dropLast ++ p_suffix.vertices := by
      simpa [vertices_comp] using
        congrArg vertices h_comp
    have : IsPrefix p_prefix.vertices.dropLast
        (p_prefix.vertices.dropLast ++ p_suffix.vertices) :=
      prefix_append p_prefix.vertices.dropLast p_suffix.vertices
    simp [hverts]
  have hverts :
      p.vertices = p_prefix.vertices.dropLast ++ p_suffix.vertices := by
    simpa [vertices_comp] using
      congrArg vertices h_comp
  have h_eq_idx :
      i = idxOf v p_prefix.vertices.dropLast := by
    have h_on_append :
        idxOf v (p_prefix.vertices.dropLast ++ p_suffix.vertices) =
        idxOf v p_prefix.vertices.dropLast :=
      idxOf_append_of_mem (l₁ := p_prefix.vertices.dropLast)
        (l₂ := p_suffix.vertices) (a := v) h_in_prefix
    simp_all only [get_eq_getElem, vertices_comp, lt_self_iff_false, i]
  have h_abs :
      idxOf v p_prefix.vertices.dropLast <
      idxOf v p_prefix.vertices.dropLast := by
    simp_all only [get_eq_getElem, vertices_comp, prefix_append, lt_self_iff_false, i]
  exact (Nat.lt_irrefl _ h_abs)

lemma mem_tail_vertices_suffix_of_two_le_count [DecidableEq V] {a b v : V} {p : Path a b}
    (h_v_in_p : v ∈ p.vertices) (h_v_count : p.vertices.count v ≥ 2) :
    let i := p.vertices.idxOf v
    let hi := List.idxOf_lt_length_iff.2 h_v_in_p
    ∀ (c : V) (p_prefix : Path a c) (p_suffix : Path c b)
      (_ : p = p_prefix.comp p_suffix) (_ : p_prefix.length = i)
      (_ : c = p.vertices.get ⟨i, hi⟩),
      v ∈ p_suffix.vertices.tail := by
  intro i hi c p_prefix p_suffix h_comp h_len_prefix h_c_eq
  have h_notin_prefix : v ∉ p_prefix.vertices.dropLast := by
    exact
      (not_mem_vertices_dropLast_of_split_at_vertex
          (a := a) (b := b) (p := p) (v := v) h_v_in_p)
        c p_prefix p_suffix h_comp h_len_prefix h_c_eq
  have h_count_split :
      (p_prefix.vertices.dropLast ++ p_suffix.vertices).count v ≥ 2 := by
    simpa [h_comp, vertices_comp] using h_v_count
  have h_count_prefix :
      (p_prefix.vertices.dropLast).count v = 0 :=
    count_eq_zero_of_not_mem h_notin_prefix
  have h_count_suffix : p_suffix.vertices.count v ≥ 2 := by
    have : (p_prefix.vertices.dropLast).count v +
        p_suffix.vertices.count v ≥ 2 := by
      simpa [count_append] using h_count_split
    simpa [h_count_prefix, zero_add] using this
  classical
  cases hvs : p_suffix.vertices with
  | nil =>
    simp [hvs] at h_count_suffix
  | cons x xs =>
    by_cases hx : x = v
    · have : v ∈ xs := by
        by_contra hnot
        have hx0 := count_eq_zero_of_not_mem (l := xs) (a := v) hnot
        have hle : 2 ≤ 1 := by
          subst h_comp hx
          simp_all only [count_append, count_cons_self, zero_add, ge_iff_le, Nat.reduceLeDiff]
        subst h_comp hx
        simp_all only [Nat.reduceLeDiff]
      simpa [hvs] using this
    · have hx2 : xs.count v ≥ 2 := by
        simpa [hvs, count_cons, hx] using h_count_suffix
      have : v ∈ xs := by
        by_contra hnot
        have hx0 := count_eq_zero_of_not_mem (l := xs) (a := v) hnot
        have hle : 2 ≤ 0 := by
          subst h_comp
          simp_all only [count_append, ne_eq, not_false_eq_true, count_cons_of_ne, add_zero,
            ge_iff_le, nonpos_iff_eq_zero, reduceCtorEq]
        exact (not_le_of_gt (by decide : 0 < 2)) hle
      simpa [hvs] using this

/-- Given vertices lists from a path composition,
the prefix path’s vertices is a prefix of the full path’s vertices. -/
lemma vertices_dropLast_isPrefix_of_vertices_eq
    {V : Type*} [Quiver V]
    {a b c : V} {p : Path a b} {p₁ : Path a c} {p₂ : Path c b}
    (h : p.vertices = p₁.vertices.dropLast ++ p₂.vertices) :
    p₁.vertices.dropLast.IsPrefix p.vertices := by
  rw [h]; exact prefix_append p₁.vertices.dropLast p₂.vertices

lemma mem_vertices_eq_end_or_mem_dropLast {a b c : V} (p : Path a b) (h : c ∈ p.vertices) :
  c = b ∨ c ∈ p.vertices.dropLast := by
  induction p with
  | nil =>
    simp [vertices_nil] at h
    subst h
    simp
  | cons p' e ih =>
    rename_i b'
    have h' : c ∈ p'.vertices ∨ c = b' := by
      simpa using (mem_vertices_cons p' e).1 h
    cases h' with
    | inl h_in_p' =>
      have ih' := ih h_in_p'
      cases ih' with
      | inl h_eq_p'_end =>
        right
        subst h_eq_p'_end
        simp_all only [true_or, imp_self, vertices_cons, concat_eq_append, mem_append, mem_cons,
          not_mem_nil, or_false, end_mem_vertices, ne_eq, cons_ne_self, not_false_eq_true,
          dropLast_append_of_ne_nil, dropLast_singleton, append_nil]
      | inr h_in_p'_dropLast =>
        simp_all only [or_true, imp_self, vertices_cons, concat_eq_append, mem_append, mem_cons,
          not_mem_nil, or_false, true_or, ne_eq, cons_ne_self, not_false_eq_true,
          dropLast_append_of_ne_nil, dropLast_singleton, append_nil]
    | inr h_eq_b =>
      left
      exact h_eq_b

/-- If we have a path p from a to b with c ∈ p.vertices,
    and c is not the end vertex b, then it appears in a proper prefix of the path. -/
lemma exists_prefix_of_mem_vertices_ne_end [DecidableEq V] {a b c : V}
    (p : Path a b) (h : c ∈ p.vertices) (h_ne : c ≠ b) :
  ∃ (p₁ : Path a c) (p₂ : Path c b), p = p₁.comp p₂ := by
  have h_cases := mem_vertices_eq_end_or_mem_dropLast p h
  cases h_cases with
  | inl h_eq =>
      contradiction
  | inr h_mem_tail =>
      let i := p.vertices.idxOf c
      have hi : i < p.vertices.length := List.idxOf_lt_length_iff.2 h
      obtain ⟨v, p₁, p₂, h_comp, h_len, h_c_eq⟩ := split_at_vertices_index p i hi
      have hvc : v = c := by
        rw [h_c_eq]
        simp [i]
      subst hvc
      exact ⟨p₁, p₂, h_comp⟩

/-- Split a path at the *last* occurrence of a vertex. -/
theorem exists_decomp_of_mem_vertices_not_mem_tail
    [DecidableEq V] {a b x : V} (p : Path a b) (hx : x ∈ p.vertices) :
    ∃ (p₁ : Path a x) (p₂ : Path x b),
      p = p₁.comp p₂ ∧ x ∉ p₂.vertices.tail := by
  classical
  induction p with
  | nil =>
      have hxa : x = a := by
        simpa [vertices_nil, List.mem_singleton] using hx
      subst hxa
      exact ⟨Path.nil, Path.nil, by simp only [comp_nil],
        by simp only [vertices_nil, tail_cons, not_mem_nil, not_false_eq_true]⟩
  | cons pPrev e ih =>
      have hx' : x ∈ pPrev.vertices ∨ x = (pPrev.cons e).end := by
        simpa using (mem_vertices_cons pPrev e).1 hx
      have h_case₁ :
          x = (pPrev.cons e).end →
          ∃ (p₁ : Path a x) (p₂ : Path x (pPrev.cons e).end),
            pPrev.cons e = p₁.comp p₂ ∧
            x ∉ p₂.vertices.tail := by
        intro hxe; subst hxe
        exact ⟨pPrev.cons e, Path.nil, by simp [comp_nil],
          by simp [vertices_nil]⟩
      have h_case₂ :
          x ∈ pPrev.vertices → x ≠ (pPrev.cons e).end →
          ∃ (p₁ : Path a x) (p₂ : Path x (pPrev.cons e).end),
            pPrev.cons e = p₁.comp p₂ ∧
            x ∉ p₂.vertices.tail := by
        intro hxPrev hxe_ne
        rcases ih hxPrev with ⟨q₁, q₂, h_prev, h_not_tail⟩
        let q₂' : Path x (pPrev.cons e).end := q₂.cons e
        have h_eq : pPrev.cons e = q₁.comp q₂' := by
          simp [q₂', h_prev]
        have h_no_tail : x ∉ q₂'.vertices.tail := by
          intro hmem
          have hmem' :
              x ∈ (q₂.vertices ++ [(pPrev.cons e).end]).tail := by
            simpa [q₂', vertices_cons, concat_eq_append] using hmem
          cases hq2 : q₂.vertices with
          | nil =>
              have : x ∈ ([] : List V) := by
                simp [hq2] at hmem'
              cases this
          | cons y ys =>
              have hx_in : x ∈ ys ++ [(pPrev.cons e).end] := by
                simpa [hq2] using hmem'
              rcases (List.mem_append.mp hx_in) with hx_ys | hx_last
              · have : x ∈ (y :: ys).tail := by simpa using hx_ys
                subst h_prev
                simp_all only [tail_cons, not_true_eq_false]
              · have : x = (pPrev.cons e).end := by
                  simpa [List.mem_singleton] using hx_last
                exact hxe_ne this
        exact ⟨q₁, q₂', h_eq, h_no_tail⟩
      cases hx' with
      | inl h_in_prefix =>
          by_cases h_eq_end : x = (pPrev.cons e).end
          · rcases h_case₁ h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
            exact ⟨p₁, p₂, h_eq, h_tail⟩
          · rcases h_case₂ h_in_prefix h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
            exact ⟨p₁, p₂, h_eq, h_tail⟩
      | inr h_eq_end =>
          rcases h_case₁ h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
          exact ⟨p₁, p₂, h_eq, h_tail⟩

end

end Quiver.Path
