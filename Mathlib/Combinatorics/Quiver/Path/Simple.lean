/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Cycle
public import Mathlib.Data.Fintype.Card

/-!
# Vertices visited by a path, and length bounds for simple paths

The vertices a path visits, as a `Set` and as a `Finset`, the decomposition of a positive-length
path at its first or last edge, and the bound `p.length ≤ card V - 1` for a path that repeats no
vertex: the material the Perron-Frobenius development needs about simple paths.

## Main definitions

* `Quiver.Path.activeVertices`, `Quiver.Path.vertexFinset`: the vertices a path visits, as a
  `Set` and as a `Finset`.

## Main statements

* `Quiver.Path.path_decomposition_first_edge`, `Quiver.Path.path_decomposition_last_edge`: a path
  of positive length splits off its first, resp. last, edge.
* `Quiver.Path.isPath_of_shortest`: a shortest path repeats no vertex.
* `Quiver.Path.length_le_card_minus_one_of_isSimple`: the length bound for simple paths.

## Tags

quiver, path, simple path, Perron-Frobenius theorem
-/

@[expose] public section

open List Finset

namespace Quiver.Path

variable {V : Type*} [Quiver V] {a b : V}

/-- Every path of positive length decomposes as an initial path followed by a final edge. -/
lemma path_decomposition_last_edge (p : Path a b) (h : 0 < p.length) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Every path of positive length decomposes as a first edge followed by the remaining path. -/
lemma path_decomposition_first_edge (p : Path a b) (h : 0 < p.length) :
    ∃ (c : V) (e : a ⟶ c) (p' : Path c b),
      p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  have hlen : p.length = (p.length - 1) + 1 := by grind
  obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p hlen
  exact ⟨c, e, p', rfl, by grind⟩

/-- The set of vertices a path visits. -/
def activeVertices (p : Path a b) : Set V := {v | v ∈ p.vertices}

@[simp] lemma mem_activeVertices {p : Path a b} {v : V} :
    v ∈ p.activeVertices ↔ v ∈ p.vertices := Iff.rfl

@[simp] lemma activeVertices_nil : activeVertices (nil : Path a a) = {a} := by
  ext; simp [activeVertices]

@[simp] lemma activeVertices_cons {c : V} (p : Path a b) (e : b ⟶ c) :
    activeVertices (p.cons e) = activeVertices p ∪ {c} := by
  ext; simp [activeVertices, or_comm]

lemma mem_vertices_to_active {p : Path a b} {x : V} (hx : x ∈ p.vertices) :
    x ∈ p.activeVertices := hx

/-- The finset of vertices a path visits. -/
def vertexFinset {V : Type*} [Quiver V] [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

/-- The set of vertices of a simple path has cardinality `p.length + 1`. -/
lemma card_vertexFinset_of_isPath {V : Type*} [Quiver V] [DecidableEq V] {a b : V}
    {p : Path a b} (hp : IsPath p) : p.vertexFinset.card = p.length + 1 := by
  simp [vertexFinset, List.toFinset_card_of_nodup hp, vertices_length]

/-- A shortest path repeats no vertex. -/
theorem isPath_of_shortest (p : Path a b) (h_min : ∀ q : Path a b, p.length ≤ q.length) :
    IsPath p := by
  by_contra h
  obtain ⟨q, hq⟩ := exists_length_lt_of_not_isPath h
  exact absurd (h_min q) (by grind)

/-- The length of a strictly simple path is at most one less than the number of vertices. -/
lemma length_le_card_minus_one_of_isSimple {V : Type*} [Fintype V] [Quiver V] {a b : V}
    (p : Path a b) (hp : p.IsPath) : p.length ≤ Fintype.card V - 1 := by
  classical
  have h := (card_vertexFinset_of_isPath hp) ▸ Finset.card_le_univ p.vertexFinset
  grind

end Quiver.Path
