/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.HypergraphLike.Basic

/-!
# Incidence hypergraphs

This file defines hypergraphs with ambient vertex, incidence, and edge types. Each active
incidence has an associated edge and an attached vertex. The underlying data is a span of sets
`V(G) ← I(G) → E(G)`, as in the span definition of a hypergraph described by
[nLab](https://ncatlab.org/nlab/show/hypergraph).

`IncidenceHypergraph` permits repeated incidences, isolated vertices, and edges with no incidences.
Its `HyperGraphLike` instance marks every active incidence as both a source and a target. The
incidence maps, support sets, links, adjacency, degree, order, uniformity, and regularity come from
that interface. Its scoped notation `V(G)`, `I(G)`, and `E(G)` denotes the active sets.

The operation `IncidenceHypergraph.dual` exchanges vertices and edges while preserving incidence
labels.
-/

@[expose] public section

variable {ν ι ε : Type*}

open Set Function HyperGraphLike

/-- An incidence hypergraph on ambient vertex, incidence, and edge types `ν`, `ι`, and `ε`. -/
structure IncidenceHypergraph (ν ι ε : Type*) where
  /-- The vertices present in the hypergraph. -/
  vertexSet : Set ν
  /-- The incidences present in the hypergraph. -/
  incidenceSet : Set ι
  /-- The edges present in the hypergraph. -/
  edgeSet : Set ε
  /-- The edge associated with an active incidence. -/
  edgeMap' : incidenceSet → ε
  /-- Every incidence is associated with an edge of the hypergraph. -/
  edgeMap'_mem : ∀ i, edgeMap' i ∈ edgeSet
  /-- The vertex attached to an active incidence. -/
  attach' : incidenceSet → ν
  /-- Every incidence is attached to a vertex of the hypergraph. -/
  attach'_mem : ∀ i, attach' i ∈ vertexSet

initialize_simps_projections IncidenceHypergraph
  (as_prefix vertexSet, as_prefix incidenceSet, as_prefix edgeSet)

namespace IncidenceHypergraph

instance : HyperGraphLike ν ι ε (IncidenceHypergraph ν ι ε) where
  verts := vertexSet
  edges := edgeSet
  incs := incidenceSet
  toEdge G i := ⟨G.edgeMap' i, G.edgeMap'_mem i⟩
  toVert G i := ⟨G.attach' i, G.attach'_mem i⟩
  IsSource G i := i ∈ G.incidenceSet
  IsTarget G i := i ∈ G.incidenceSet
  mem_incs_iff := by simp

variable {G H : IncidenceHypergraph ν ι ε} {e : ε} {v : ν} {k : ℕ∞}

/-- Two incidence hypergraphs are equal if their active sets and incidence maps agree. -/
@[ext]
protected lemma ext [Nonempty ν] [Nonempty ε] {G H : IncidenceHypergraph ν ι ε}
    (hV : V(G) = V(H)) (hI : I(G) = I(H)) (hE : E(G) = E(H))
    (hEdge : ∀ i ∈ I(G), edgeMap G i = edgeMap H i)
    (hAttach : ∀ i ∈ I(G), attach G i = attach H i) : G = H := by
  cases G
  cases H
  cases hI
  simp_all [edgeMap, attach, toEdge, toVert, verts, incs, edges, funext_iff]

/-! ### Duality -/

/-- The incidence dual, obtained by exchanging vertices and edges while preserving incidences. -/
@[simps vertexSet incidenceSet edgeSet]
def dual (G : IncidenceHypergraph ν ι ε) : IncidenceHypergraph ε ι ν where
  vertexSet := E(G)
  incidenceSet := I(G)
  edgeSet := V(G)
  edgeMap' := G.attach'
  edgeMap'_mem := G.attach'_mem
  attach' := G.edgeMap'
  attach'_mem := G.edgeMap'_mem

@[simp]
lemma edgeMap_dual [Nonempty ν] (G : IncidenceHypergraph ν ι ε) (i : ι) :
    edgeMap G.dual i = attach G i := rfl

@[simp]
lemma attach_dual [Nonempty ε] (G : IncidenceHypergraph ν ι ε) (i : ι) :
    attach G.dual i = edgeMap G i := rfl

@[simp]
lemma dual_dual (G : IncidenceHypergraph ν ι ε) : G.dual.dual = G := rfl

@[simp]
lemma mem_incVerts_dual : e ∈ incVerts G.dual v ↔ v ∈ incVerts G e := mem_incEdges (G := G)

lemma dual_bijective : Bijective (dual : IncidenceHypergraph ν ι ε → _) :=
  ⟨LeftInverse.injective dual_dual, RightInverse.surjective dual_dual⟩

@[simp]
lemma dual_inj : G.dual = H.dual ↔ G = H := dual_bijective.injective.eq_iff

@[simp]
lemma degree_dual (G : IncidenceHypergraph ν ι ε) (e : ε) : degree G.dual e = order G e := rfl

@[simp]
lemma order_dual (G : IncidenceHypergraph ν ι ε) (v : ν) : order G.dual v = degree G v := rfl

@[simp]
lemma isUniform_dual : IsUniform G.dual k ↔ IsRegular G k := Iff.rfl

@[simp]
lemma isRegular_dual : IsRegular G.dual k ↔ IsUniform G k := Iff.rfl

end IncidenceHypergraph
