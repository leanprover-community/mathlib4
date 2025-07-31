/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Finset.Dedup

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
lemma end_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : «end» (p.cons e) = c := rfl

/-- The list of vertices in a path, including the start and end vertices. -/
def vertices {a : V} : ∀ {b : V}, Path a b → List V
  | _, nil => [a]
  | _, cons p e => (p.vertices).concat («end» (p.cons e))

/-- The set of vertices in a path. -/
def vertices_set {a b : V} (p : Path a b) : Set V :=
  {v | v ∈ p.vertices}

/-- The finset of vertices in a path. -/
def vertices_finset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

/-- The finset of vertices in a path, excluding the final vertex. -/
def init_finset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.dropLast.toFinset

@[simp]
lemma mem_vertices_set_iff {a b : V} (p : Path a b) (v : V) :
    v ∈ p.vertices_set ↔ v ∈ p.vertices := Iff.rfl

@[simp]
lemma mem_vertices_finset_iff [DecidableEq V] {a b : V} (p : Path a b) {x : V} :
    x ∈ p.vertices_finset ↔ x ∈ p.vertices :=
  List.mem_toFinset

@[simp]
lemma mem_init_finset_iff [DecidableEq V] {a b : V} (p : Path a b) {x : V} :
    x ∈ p.init_finset ↔ x ∈ p.vertices.dropLast :=
  List.mem_toFinset

lemma vertices_nil (a : V) : (nil : Path a a).vertices = [a] := rfl

@[simp]
lemma vertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  (p.cons e).vertices = p.vertices.concat c := rfl

-- Vertices of a path are always non-empty
lemma vertices_nonempty' {V : Type*} [Quiver V] {a b : V} (p : Path a b) :
    p.vertices.length > 0 := by
  induction p with
  | nil => simp only [vertices_nil, List.length_cons, List.length_nil, Nat.zero_add, gt_iff_lt,
      Nat.lt_add_one]
  | cons p' e ih =>
    rw [vertices_cons]
    simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
      zero_add, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, ih, Nat.lt_one_iff, pos_of_gt, or_self]

lemma mem_vertices_set {a b : V} (p : Path a b) (v : V) :
    v ∈ p.vertices_finset' ↔ v ∈ p.vertices := Iff.rfl

/-- The vertex list of `cons` — convenient `simp` form. -/
lemma mem_vertices_cons {a b c : V} (p : Path a b)
    (e : b ⟶ c) {x : V} :
    x ∈ (p.cons e).vertices ↔ x ∈ p.vertices ∨ x = c := by
  simp only [vertices_cons]
  simp_all only [concat_eq_append, mem_append, mem_cons, not_mem_nil, or_false]

lemma vertices_set_nil {a : V} : vertices_set (nil : Path a a) = {a} := by
  simp only [vertices_set, vertices_nil, List.mem_singleton, Set.ext_iff, Set.mem_singleton_iff]
  exact fun x ↦ Set.mem_setOf

@[simp]
lemma vertices_set_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  vertices_set (p.cons e) = vertices_set p ∪ {c} := by
  simp only [Set.union_singleton]
  ext v
  simp only [mem_vertices_set_iff, Set.mem_insert_iff]
  rw [or_comm]; exact mem_vertices_cons p e

/-- The length of vertices list equals path length plus one -/
@[simp]
lemma vertices_length {V : Type*} [Quiver V] {a b : V} (p : Path a b) :
    p.vertices.length = p.length + 1 := by
  induction p with
  | nil => simp only [vertices_nil, List.length_cons, List.length_nil, zero_add, length_nil]
  | cons p' e ih =>
    simp only [vertices_cons, length_cons, List.length_concat, ih]

lemma vertices_nonempty {a : V} {b : V} (p : Path a b) : p.vertices ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, vertices_length]; omega

/-- The head of the vertices list is the start vertex -/
@[simp]
lemma vertices_head? {a b : V} (p : Path a b) : p.vertices.head? = some a := by
  induction p with
  | nil => simp only [vertices_nil, List.head?_cons]
  | cons p' e ih =>
    simp only [vertices_cons]
    have : ¬p'.vertices.isEmpty := by
      simp_all only [List.isEmpty_iff]
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      simp_all only [List.head?_nil, reduceCtorEq]
    simp
    simp_all only [List.isEmpty_iff, Option.getD_some]

@[simp]
lemma length_toPath {a b : V} (e : a ⟶ b) : (e.toPath).length = 1 := rfl

@[simp]
lemma vertices_getLast {a b : V} (p : Path a b) (h : p.vertices ≠ []) :
  p.vertices.getLast h = b := by
  induction p with
  | nil => simp only [vertices_nil, List.getLast_singleton]
  | cons p' e ih =>
    simp only [vertices_cons]
    rw [@List.getLast_concat']

@[simp]
lemma vertices_comp {a b c : V} (p : Path a b) (q : Path b c) :
  (p.comp q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction q with
  | nil =>
    simp only [comp_nil, vertices_nil]
    have h_nonempty : p.vertices.length > 0 := vertices_nonempty' p
    have h_ne_nil : p.vertices ≠ [] := List.ne_nil_of_length_pos h_nonempty
    rw [← List.dropLast_append_getLast h_ne_nil, vertices_getLast p h_ne_nil]
    simp_all only [gt_iff_lt, ne_eq, List.cons_ne_self, not_false_eq_true,
      List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
  | cons q' e ih =>
    simp only [comp_cons, vertices_cons, ih, List.concat_eq_append]
    rw [List.append_assoc]

lemma start_mem_vertices {a b : V} (p : Path a b) : a ∈ p.vertices := by
  induction p with
  | nil => simp only [vertices_nil, List.mem_cons, List.not_mem_nil, or_false]
  | cons p' e ih =>
    simp only [vertices_cons]
    simp_all only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, true_or]

@[simp] lemma length_eq_zero_iff {a : V} (p : Path a a) :
    p.length = 0 ↔ p = Path.nil := by
  cases p
  · simp only [length_nil]
  · constructor
    · intro h; cases h
    · intro h; cases h

/-- Given vertices lists from a path composition, the prefix path's vertices is a prefix of
the full path's vertices -/
lemma isPrefix_dropLast_of_comp_eq {V : Type*}
    [Quiver V] {a b c : V} {p : Path a b} {p₁ : Path a c} {p₂ : Path c b}
    (h : p.vertices = p₁.vertices.dropLast ++ p₂.vertices) :
    p₁.vertices.dropLast.IsPrefix p.vertices := by
  rw [h]
  exact List.prefix_append p₁.vertices.dropLast p₂.vertices

/-- The head of the vertices list is the start vertex. -/
@[simp]
lemma vertices_head_eq_start {a b : V} (p : Path a b) :
    p.vertices.head (vertices_nonempty p) = a := by
  induction p with
  | nil => simp only [vertices_nil, List.head_cons]
  | cons p' _ ih =>
    simp only [vertices_cons, List.concat_eq_append]
    have : p'.vertices ≠ [] := vertices_nonempty p'
    simp only [List.head_append_of_ne_nil this]
    exact ih

/-- The last element of the vertices list is the end vertex. -/
lemma vertices_getLast_eq_end {a b : V} (p : Path a b) :
  p.vertices.getLast (vertices_nonempty p) = b := by
  exact vertices_getLast p (vertices_nonempty p)

lemma end_prefix_eq_get_vertices {a b c : V} (p₁ : Path a c) (p₂ : Path c b) :
    c = (p₁.comp p₂).vertices.get
        ⟨p₁.length, by
  simp only [vertices_comp, List.length_append, List.length_dropLast,
    vertices_length, add_tsub_cancel_right, lt_add_iff_pos_right, add_pos_iff,
    Nat.lt_one_iff, pos_of_gt, or_true]⟩ := by
  simp only [List.get_eq_getElem, vertices_comp, List.length_dropLast, vertices_length,
    add_tsub_cancel_right, le_refl, List.getElem_append_right, tsub_self, List.getElem_zero,
    vertices_head_eq_start]

@[simp]
lemma vertices_toPath {i j : V} (e : i ⟶ j) :
    (e.toPath).vertices = [i, j] := by
  change (Path.nil.cons e).vertices = [i, j]
  simp [vertices_cons, vertices_nil];

lemma vertices_toPath_tail {i j : V} (e : i ⟶ j) :
    (e.toPath).vertices.tail = [j] := by
  simp [vertices_toPath]

/-- If a composition is `nil`, the left component must be `nil`
    (proved via lengths, avoiding dependent pattern-matching). -/
lemma nil_of_comp_eq_nil_left {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = (Path.nil : Path a a)) : p.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_right this-- Nat.eq_zero_of_add_eq_zero_left this

/-- If a composition is `nil`, the right component must be `nil` -/
lemma nil_of_comp_eq_nil_right {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = (Path.nil : Path a a)) : q.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_left this

@[simp]
lemma end_mem_vertices {a b : V} (p : Path a b) : b ∈ p.vertices := by
  have h₁ : p.vertices.getLast (vertices_nonempty p) = b :=
    vertices_getLast p (vertices_nonempty p)
  have h₂ := List.getLast_mem (l := p.vertices) (vertices_nonempty p)
  simpa [h₁] using h₂

lemma mem_vertices_to_set {V : Type*} [Quiver V]
    {a b : V} {p : Path a b} {x : V} :
    x ∈ p.vertices → x ∈ p.vertices_set:= by
  intro hx
  induction p with
  | nil =>
      simpa [vertices_nil, vertices_set_nil] using hx
  | cons p' e ih =>
      rcases (mem_vertices_cons (p := p') (e := e) (x := x)).1 hx with h | rfl
      · have : x ∈ p'.vertices_set:= ih h
        simp_all only [imp_self, vertices_cons, concat_eq_append, mem_append, mem_cons,
          not_mem_nil, or_false, true_or, vertices_set_cons, Set.union_singleton,
          Set.mem_insert_iff, or_true]
      · simp [vertices_set_cons]

end Quiver.Path
