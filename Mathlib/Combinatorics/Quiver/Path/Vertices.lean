/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Quiver.Path
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

lemma start_mem_vertices {a b : V} (p : Path a b) : a ∈ p.vertices := by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

/-- The head of the vertices list is the start vertex -/
@[simp]
lemma vertices_head? {a b : V} (p : Path a b) : p.vertices.head? = some a := by
  induction p with
  | nil => simp only [vertices_nil, head?_cons]
  | cons p' e ih => simp [ih]

/-- The head of the vertices list is the start vertex. -/
@[simp]
lemma vertices_head_eq {a b : V} (p : Path a b) (h : p.vertices ≠ [] := p.vertices_ne_nil) :
    p.vertices.head h = a := by
  induction p with
  | nil => simp only [vertices_nil, head_cons]
  | cons p' _ ih => simp [head_append_of_ne_nil (vertices_ne_nil p'), ih]

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
lemma dropLast_append_end_eq {a b : V} (p : Path a b) :
    p.vertices.dropLast ++ [b] = p.vertices := by
  simp_rw [← p.vertices_getLast p.vertices_ne_nil, dropLast_concat_getLast]

@[simp]
lemma vertices_comp {a b c : V} (p : Path a b) (q : Path b c) :
  (p.comp q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction q with
  | nil => simp
  | cons q' e ih => simp [ih]

@[simp] lemma length_eq_zero_iff {a : V} (p : Path a a) :
    p.length = 0 ↔ p = Path.nil := by
  cases p <;> tauto

lemma vertices_comp_get_length_eq {a b c : V} (p₁ : Path a c) (p₂ : Path c b)
    (h : p₁.length < (p₁.comp p₂).vertices.length := by simp) :
    (p₁.comp p₂).vertices.get ⟨p₁.length, h⟩ = c := by
  simp

@[simp]
lemma vertices_toPath {i j : V} (e : i ⟶ j) :
    e.toPath.vertices = [i, j] := by
  change (Path.nil.cons e).vertices = [i, j]
  simp

lemma vertices_toPath_tail {i j : V} (e : i ⟶ j) :
    e.toPath.vertices.tail = [j] := by
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

variable {a b : V} (p : Path a b)

open List

/-- Given a path `p : Path a b` and an index `n ≤ p.length`,
    we can split `p = p₁.comp p₂` with `p₁.length = n`. -/
theorem exists_eq_comp_of_le_length {n : ℕ} (hn : n ≤ p.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ p₁.length = n := by
  induction p generalizing n with
  | nil =>
    obtain ⟨rfl⟩ : n = 0 := by simpa using hn
    exact ⟨a, Path.nil, Path.nil, by simp, rfl⟩
  | @cons _ c p' e ih =>
    rw [length_cons] at hn
    rcases (Nat.le_succ_iff).1 hn with h | rfl
    · obtain ⟨d, p₁, p₂, hp, hl⟩ := ih h
      exact ⟨d, p₁, p₂.cons e, by simp [hp], hl⟩
    · exact ⟨c, p'.cons e, Path.nil, by simp, by simp⟩

/-- `split_at_vertex` decomposes a path `p` at the vertex sitting in
    position `i` of its `vertices` -/
theorem exists_eq_comp_and_length_eq_of_lt_length (n : ℕ) (hn : n < p.vertices.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ p₁.length = n ∧ v = p.vertices[n] := by
  have hn_le_len : n ≤ p.length := by
    rw [vertices_length] at hn
    exact Nat.le_of_lt_succ hn
  obtain ⟨v, p₁, p₂, rfl, rfl⟩ := p.exists_eq_comp_of_le_length hn_le_len
  exact ⟨v, p₁, p₂, rfl, rfl, by simp⟩

/-- If a vertex `v` occurs in the list of vertices of a path `p : Path a b`, then `p` can be
decomposed as a concatenation of a subpath from `a` to `v` and a subpath from `v` to `b`. -/
theorem exists_eq_comp_of_mem_vertices {v : V} (hv : v ∈ p.vertices) :
    ∃ (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ := by
  obtain ⟨n, hn, rfl⟩ : ∃ n, ∃ hn : n < p.vertices.length, v = p.vertices[n] :=
    exists_mem_iff_getElem.mp ⟨v, hv, rfl⟩
  obtain ⟨v, p₁, p₂, hp, hv, rfl⟩ := p.exists_eq_comp_and_length_eq_of_lt_length n hn
  exact ⟨p₁, p₂, hp⟩

/-- Split a path at the *last* occurrence of a vertex. -/
theorem exists_eq_comp_and_notMem_tail_of_mem_vertices {v : V} (hv : v ∈ p.vertices) :
    ∃ (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
  induction p with
  | nil =>
    have hxa : v = a := by
      simpa [vertices_nil, List.mem_singleton] using hv
    subst hxa
    exact ⟨Path.nil, Path.nil, by simp only [comp_nil],
      by simp only [vertices_nil, tail_cons, not_mem_nil, not_false_eq_true]⟩
  | cons pPrev e ih =>
    have hv' : v ∈ pPrev.vertices ∨ v = (pPrev.cons e).end := by
      simpa using (mem_vertices_cons pPrev e).1 hv
    have h_case₁ : v = (pPrev.cons e).end → ∃ (p₁ : Path a v) (p₂ : Path v (pPrev.cons e).end),
        pPrev.cons e = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
      rintro rfl
      exact ⟨pPrev.cons e, Path.nil, by simp [comp_nil], by simp [vertices_nil]⟩
    have h_case₂ : v ∈ pPrev.vertices → v ≠ (pPrev.cons e).end →
        ∃ (p₁ : Path a v) (p₂ : Path v (pPrev.cons e).end),
          pPrev.cons e = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
      intro hxPrev hxe_ne
      obtain ⟨q₁, q₂, h_prev, h_not_tail⟩ := ih hxPrev
      let q₂' : Path v (pPrev.cons e).end := q₂.cons e
      have h_no_tail : v ∉ q₂'.vertices.tail := by grind [vertices_cons, end_cons]
      exact ⟨q₁, q₂', by simp [q₂', h_prev], h_no_tail⟩
    cases hv' with
    | inl h_in_prefix =>
      by_cases h_eq_end : v = (pPrev.cons e).end
      · exact h_case₁ h_eq_end
      · exact h_case₂ h_in_prefix h_eq_end
    | inr h_eq_end => exact h_case₁ h_eq_end

end

end Quiver.Path
