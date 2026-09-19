/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Mathlib.Combinatorics.Compactness
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# List coloring of simple graphs

This file defines colorings in which each vertex has a prescribed set of available colors.
It also proves the compactness theorem for finite lists: a graph has a coloring from its lists if
and only if every finite induced subgraph does.

## Main definitions

* `SimpleGraph.ListColoring`: a proper coloring that uses an available color at every vertex.
* `SimpleGraph.ListColoring.induce`: the restriction of a list coloring to an induced subgraph.

## Main results

* `SimpleGraph.nonempty_listColoring_of_finite_induced`: list-coloring compactness.
* `SimpleGraph.nonempty_listColoring_iff_finite_induced`: the finite-induced-subgraph
  characterization of list colorability.

## References

* N. G. de Bruijn and P. Erdős, "A colour problem for infinite graphs and a problem in the theory
  of relations", 1951.
* R. Rado, "Axiomatic treatment of rank in infinite sets", 1949.

-/

@[expose] public section

universe u v

namespace SimpleGraph

variable {V : Type u} {C : Type v} {G : SimpleGraph V} {lists : V → Set C}

/-- A proper coloring that assigns to every vertex a color from its prescribed set. -/
structure ListColoring (G : SimpleGraph V) (lists : V → Set C) where
  /-- The underlying proper coloring. -/
  toColoring : G.Coloring C
  /-- The color of each vertex belongs to its prescribed set. -/
  mem_lists (vertex : V) : toColoring vertex ∈ lists vertex

/-- Restrict a list coloring to an induced subgraph. -/
def ListColoring.induce (coloring : G.ListColoring lists) (s : Set V) :
    (G.induce s).ListColoring (fun vertex : s ↦ lists vertex) where
  toColoring := coloring.toColoring.comap (Embedding.induce s).toHom
  mem_lists vertex := coloring.mem_lists vertex

/-- If every finite induced subgraph has a coloring from prescribed finite sets of colors, then the
whole graph has such a coloring. -/
theorem nonempty_listColoring_of_finite_induced (lists : V → Set C)
    (h_lists : ∀ vertex, (lists vertex).Finite)
    (h : ∀ (s : Set V) (_ : s.Finite),
      Nonempty ((G.induce s).ListColoring (fun vertex : s ↦ lists vertex))) :
    Nonempty (G.ListColoring lists) := by
  classical
  letI (vertex : V) : Fintype (lists vertex) := (h_lists vertex).fintype
  let localColoring (s : Set V) (hs : s.Finite) :
      (G.induce s).ListColoring (fun vertex : s ↦ lists vertex) :=
    (h s hs).some
  obtain ⟨color, hcolor⟩ := Set.Finite.rado_selection_subtype
    (β := fun vertex ↦ lists vertex) (fun s hs vertex ↦
      ⟨(localColoring s hs).toColoring vertex, (localColoring s hs).mem_lists vertex⟩)
  refine ⟨⟨Coloring.mk (fun vertex ↦ color vertex) ?_, fun vertex ↦ (color vertex).property⟩⟩
  intro vertex₁ vertex₂ hadj
  obtain ⟨t, ht, hst, hagree⟩ :=
    hcolor {vertex₁, vertex₂} ((Set.finite_singleton vertex₂).insert vertex₁)
  have h₁ : vertex₁ ∈ ({vertex₁, vertex₂} : Set V) := by simp
  have h₂ : vertex₂ ∈ ({vertex₁, vertex₂} : Set V) := by simp
  rw [congrArg Subtype.val (hagree ⟨vertex₁, h₁⟩),
    congrArg Subtype.val (hagree ⟨vertex₂, h₂⟩)]
  exact (localColoring t ht).toColoring.valid (induce_adj.2 hadj)

/-- A graph has a coloring from prescribed finite sets of colors if and only if every finite
induced subgraph does. -/
theorem nonempty_listColoring_iff_finite_induced (lists : V → Set C)
    (h_lists : ∀ vertex, (lists vertex).Finite) :
    Nonempty (G.ListColoring lists) ↔
      ∀ (s : Set V) (_ : s.Finite),
        Nonempty ((G.induce s).ListColoring (fun vertex : s ↦ lists vertex)) := by
  constructor
  · rintro ⟨coloring⟩ s _
    exact ⟨coloring.induce s⟩
  · exact G.nonempty_listColoring_of_finite_induced lists h_lists

end SimpleGraph
