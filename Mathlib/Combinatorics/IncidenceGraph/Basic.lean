/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.IncidenceHypergraph.Basic

/-!
# Incidence graphs

This file defines multigraphs by extending `IncidenceHypergraph` with a pairing of the two
incidences of each edge. The two incidences remain distinct for a loop.

The `HyperGraphLike` instance inherits the incidence maps, support sets, links, adjacency, and
incidence counts from the underlying hypergraph. Its scoped notation `V(G)`, `I(G)`, and `E(G)`
denotes the active vertex, incidence, and edge sets.
-/

@[expose] public section

open Set HyperGraphLike

/-- An incidence based multigraph with two paired incidences for every edge. -/
structure IncidenceGraph (ν ι ε : Type*) extends IncidenceHypergraph ν ι ε where
  /-- Every edge has an incidence associated with it. -/
  edgeMap_range : range edgeMap' = edgeSet
  /-- The other incidence of the same edge. -/
  other' : incidenceSet → incidenceSet
  /-- The two incidences of an edge are distinct, including for a loop. -/
  other'_ne : ∀ i, other' i ≠ i
  /-- The other incidence is associated with the same edge. -/
  edgeMap'_other' : ∀ i, edgeMap' (other' i) = edgeMap' i
  /-- Every incidence of an edge is one of its two paired incidences. -/
  edgeMap'_eq : ∀ i j, edgeMap' i = edgeMap' j → j = i ∨ j = other' i

variable {ν ι ε : Type*}

namespace IncidenceGraph

instance : HyperGraphLike ν ι ε (IncidenceGraph ν ι ε) where
  verts G := V(G.toIncidenceHypergraph)
  edges G := E(G.toIncidenceHypergraph)
  incs G := I(G.toIncidenceHypergraph)
  toEdge G := toEdge G.toIncidenceHypergraph
  toVert G := toVert G.toIncidenceHypergraph
  IsSource G := IsSource G.toIncidenceHypergraph
  IsTarget G := IsTarget G.toIncidenceHypergraph
  mem_incs_iff {G} := mem_incs_iff (G := G.toIncidenceHypergraph)

/-- Two incidence graphs are equal if their active sets and incidence maps agree. -/
@[ext]
lemma ext {G H : IncidenceGraph ν ι ε} (hV : V(G) = V(H)) (hI : I(G) = I(H)) (hE : E(G) = E(H))
    (hEdge : ∀ (i : ι) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)), G.edgeMap' ⟨i, hiG⟩ = H.edgeMap' ⟨i, hiH⟩)
    (hAttach : ∀ (i : ι) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)),
    G.attach' ⟨i, hiG⟩ = H.attach' ⟨i, hiH⟩) : G = H := by
  cases G with | mk G hG Gother hnG heG huG =>
  cases H with | mk H hH Hother hnH heH huH =>
  obtain rfl : G = H := IncidenceHypergraph.ext hV hI hE hEdge hAttach
  obtain rfl : Gother = Hother :=
    funext fun i ↦ ((huG i (Hother i) (heH i).symm).resolve_left (hnH i)).symm
  rfl

end IncidenceGraph
