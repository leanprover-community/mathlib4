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
  simp only [vertices_nil, List.mem_singleton, Set.ext_iff, Set.mem_singleton_iff]
  exact fun x ↦ Set.mem_setOf

/-- The length of vertices list equals path length plus one -/
@[simp]
lemma vertices_length {V : Type*} [Quiver V] {a b : V} (p : Path a b) :
    p.vertices.length = p.length + 1 := by
  induction p with
  | nil => simp only [vertices_nil, List.length_cons, List.length_nil, zero_add, length_nil]
  | cons p' e ih =>
    simp only [vertices_cons, length_cons, List.length_concat, ih]

lemma length_vertices_pos {a b : V} (p : Path a b) :
    0 < p.vertices.length := by simp

lemma vertices_ne_nil {a : V} {b : V} (p : Path a b) : p.vertices ≠ [] := by
  simp [← List.length_pos_iff_ne_nil]

/-- The head of the vertices list is the start vertex -/
@[simp]
lemma vertices_head? {a b : V} (p : Path a b) : p.vertices.head? = some a := by
  induction p with
  | nil => simp only [vertices_nil, List.head?_cons]
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
  | nil => simp only [vertices_nil, List.getLast_singleton]
  | cons p' e ih => simp

@[simp]
lemma vertices_comp {a b c : V} (p : Path a b) (q : Path b c) :
  (p.comp q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction q with
  | nil => simpa using (List.dropLast_append_getLast p.vertices_ne_nil).symm
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
  | nil => simp only [vertices_nil, List.head_cons]
  | cons p' _ ih => simp [List.head_append_of_ne_nil (vertices_ne_nil p'), ih]

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
  have h₂ := List.getLast_mem (l := p.vertices) (vertices_ne_nil p)
  simpa [h₁] using h₂

end Quiver.Path
