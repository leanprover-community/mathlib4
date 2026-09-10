/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.WLOG

/-!
# Incidence hypergraphs

This file defines hypergraphs with ambient vertex, incidence, and edge types. Each active
incidence has an associated edge and an attached vertex.

## Main definitions

* `IncidenceHypergraph`: the incidence hypergraph structure.
* `IncidenceHypergraph.IsLink`: two distinct incidences of an edge with specified attached vertices.
* `IncidenceHypergraph.Inc`: the vertices attached to incidences of an edge.
* `IncidenceHypergraph.Adj`: two vertices are joined by an `IsLink`.

## Implementation notes

The underlying mathematical data is a span of sets `V(G) ← I(G) → E(G)`, with maps induced by
`attach` and `edgeMap`. This is the span definition of a hypergraph described by
[nLab](https://ncatlab.org/nlab/show/hypergraph).

This is a quite permissive definition of a hypergraph, where there can be multiple incidences
between an edge and a vertex, and there could be isolated vertices and edges.

## Notation

Within the `IncidenceHypergraph` scope, `V(G)`, `I(G)`, and `E(G)` denote the vertex, incidence,
and edge sets.

## File organization

The subgraph order and empty-incidence constructions are developed in
`Mathlib.Combinatorics.IncidenceHypergraph.Subgraph`.

-/

@[expose] public section

variable {ν ι ε : Type*}

open Set

/-- A incidence based hypergraph definition on ambient vertex, incidence and edge types `ν`, `ι`
and `ε`. -/
structure IncidenceHypergraph (ν ι ε : Type*) where
  /-- The vertices present in the graph. -/
  vertexSet : Set ν
  /-- The incidences present in the graph -/
  incidenceSet : Set ι
  /-- The edges present in the graph -/
  edgeSet : Set ε
  /-- The edge which the incidence is associated with. -/
  edgeMap' : incidenceSet → ε
  /-- Every incidence is associated with an edge of the graph. -/
  edgeMap'_mem : ∀ i, edgeMap' i ∈ edgeSet
  /-- The vertex which the incidence is attached to. -/
  attach' : incidenceSet → ν
  /-- Every incidence is attached to a vertex of the graph. -/
  attach'_mem : ∀ i, attach' i ∈ vertexSet

initialize_simps_projections IncidenceHypergraph
  (as_prefix vertexSet, as_prefix incidenceSet, as_prefix edgeSet)

namespace IncidenceHypergraph

/-- `V(G)` denotes the `vertexSet` of a IncidenceHypergraph `G`. -/
scoped notation "V(" G ")" => IncidenceHypergraph.vertexSet G

/-- `I(G)` denotes the `incidenceSet` of a IncidenceHypergraph `G`. -/
scoped notation "I(" G ")" => IncidenceHypergraph.incidenceSet G

/-- `E(G)` denotes the `edgeSet` of a IncidenceGraph `G`. -/
scoped notation "E(" G ")" => IncidenceHypergraph.edgeSet G

variable {G H : IncidenceHypergraph ν ι ε} {e : ε} {u v : ν} {i j : ι}

/-! ### Incidence maps -/

attribute [simp] edgeMap'_mem attach'_mem

lemma range_edgeMap'_subset : range G.edgeMap' ⊆ E(G) := by
  rintro _ ⟨i, rfl⟩
  exact G.edgeMap'_mem i

lemma range_attach'_subset : range G.attach' ⊆ V(G) := by
  rintro _ ⟨i, rfl⟩
  exact G.attach'_mem i

open Classical in
noncomputable def attach [Nonempty ν] (G : IncidenceHypergraph ν ι ε) (i : ι) : ν :=
  if h : i ∈ I(G) then G.attach' ⟨i, h⟩ else Classical.arbitrary ν

lemma attach_mem [Nonempty ν] (hi : i ∈ I(G)) : attach G i ∈ V(G) := by
  simp [attach, hi]

@[simp]
lemma attach'_eq_attach [Nonempty ν] (i : I(G)) : G.attach' i = attach G i := by
  simp [attach]

open Classical in
noncomputable def edgeMap [Nonempty ε] (G : IncidenceHypergraph ν ι ε) (i : ι) : ε :=
  if h : i ∈ I(G) then G.edgeMap' ⟨i, h⟩ else Classical.arbitrary ε

lemma edgeMap_mem [Nonempty ε] (hi : i ∈ I(G)) : edgeMap G i ∈ E(G) := by
  simp [edgeMap, hi]

@[simp]
lemma edgeMap'_eq_edgeMap [Nonempty ε] (i : I(G)) : G.edgeMap' i = edgeMap G i := by
  simp [edgeMap]

lemma incidenceSet_eq_empty_of_vertexSet_eq_empty (hV : V(G) = ∅) : I(G) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun i hi ↦ ?_
  simpa [hV] using G.attach'_mem ⟨i, hi⟩

lemma incidenceSet_eq_empty_of_edgeSet_eq_empty (hE : E(G) = ∅) : I(G) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun i hi ↦ ?_
  simpa [hE] using G.edgeMap'_mem ⟨i, hi⟩

/-! ### Incidence vertices of an edge -/

/-- Set of vertices attached to an edge via some incidence. Multiplicity of incidence is ignored. -/
def endSet (G : IncidenceHypergraph ν ι ε) (e : ε) : Set ν :=
  G.attach' '' G.edgeMap' ⁻¹' {e}

lemma mem_inc_iff_exists_incidence [Nonempty ε] [Nonempty ν] :
    u ∈ G.endSet e ↔ ∃ i, i ∈ I(G) ∧ G.edgeMap i = e ∧ G.attach i = u := by
  constructor
  · rintro ⟨i, rfl, rfl⟩
    use i, i.prop
    simp
  rintro ⟨i, hi, rfl, rfl⟩
  use ⟨i, hi⟩
  simp

lemma endSet_subset_vertexSet : G.endSet e ⊆ V(G) := by
  rintro u ⟨i, _, rfl⟩
  exact G.attach'_mem i

lemma mem_edgeSet_of_mem_endSet (h : u ∈ G.endSet e) : e ∈ E(G) := by
  obtain ⟨i, rfl, _⟩ := h
  exact G.edgeMap'_mem i

/-! ### Links -/

/-- `G.IsLink e u v` means that two distinct incidences of `e` are attached to `u` and `v`.
The vertices may coincide, but a single incidence cannot witness a link to itself. -/
def IsLink (G : IncidenceHypergraph ν ι ε) (e : ε) (u v : ν) : Prop :=
  ∃ i j : I(G), i ≠ j ∧ G.edgeMap' i = e ∧ G.edgeMap' j = e ∧ G.attach' i = u ∧ G.attach' j = v

lemma isLink_iff_exists_incidence [Nonempty ε] [Nonempty ν] :
    G.IsLink e u v ↔ ∃ i j, i ∈ I(G) ∧ j ∈ I(G) ∧ i ≠ j ∧ G.edgeMap i = e ∧ G.edgeMap j = e ∧
    G.attach i = u ∧ G.attach j = v := by
  simp only [IsLink, ne_eq, edgeMap'_eq_edgeMap, attach'_eq_attach, Subtype.exists,
    exists_and_right, Subtype.mk.injEq, exists_prop, exists_and_left]
  grind

@[symm]
lemma IsLink.symm (h : G.IsLink e u v) : G.IsLink e v u := by
  rcases h with ⟨i, j, hij, he, hf, hu, hv⟩
  exact ⟨j, i, hij.symm, hf, he, hv, hu⟩

instance : Std.Symm (G.IsLink e) where
  symm _ _ := IsLink.symm

lemma isLink_comm : G.IsLink e u v ↔ G.IsLink e v u :=
  ⟨.symm, .symm⟩

lemma isLink_attach [Nonempty ε] [Nonempty ν] (hi : i ∈ I(G)) (hj : j ∈ I(G)) (hij : i ≠ j)
    (he : G.edgeMap' ⟨i, hi⟩ = G.edgeMap' ⟨j, hj⟩) :
    G.IsLink (G.edgeMap' ⟨i, hi⟩) (G.attach' ⟨i, hi⟩) (G.attach' ⟨j, hj⟩) :=
  ⟨⟨i, hi⟩, ⟨j, hj⟩, Subtype.coe_ne_coe.mp hij, rfl, he.symm, rfl, rfl⟩

@[grind →]
lemma IsLink.left_mem_endSet (h : G.IsLink e u v) : u ∈ G.endSet e := by
  obtain ⟨i, j, _, hi, _, hu, _⟩ := h
  exact ⟨i, hi, hu⟩

@[grind →]
lemma IsLink.right_mem_endSet (h : G.IsLink e u v) : v ∈ G.endSet e :=
  h.symm.left_mem_endSet

lemma IsLink.edge_mem (h : G.IsLink e u v) : e ∈ E(G) :=
  mem_edgeSet_of_mem_endSet h.left_mem_endSet

lemma IsLink.left_mem (h : G.IsLink e u v) : u ∈ V(G) :=
  endSet_subset_vertexSet h.left_mem_endSet

lemma IsLink.right_mem (h : G.IsLink e u v) : v ∈ V(G) :=
  h.symm.left_mem

lemma IsLink.pair_subset_endSet (h : G.IsLink e u v) : {u, v} ⊆ G.endSet e := by
  rintro w (rfl | rfl)
  · exact h.left_mem_endSet
  exact h.right_mem_endSet

@[simp]
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e u v :=
  mt IsLink.edge_mem he

/-- Incidences at different vertices necessarily give distinct incidence witnesses. -/
lemma isLink_iff_subset_endSet_of_ne (huv : u ≠ v) : G.IsLink e u v ↔ {u, v} ⊆ G.endSet e := by
  rw [Set.pair_subset_iff]
  refine ⟨fun h ↦ ⟨h.left_mem_endSet, h.right_mem_endSet⟩, ?_⟩
  rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩
  exact ⟨i, j, fun hij ↦ huv (congrArg G.attach' hij), hi, hj, rfl, rfl⟩

/-! ### Adjacency -/

/-- `G.Adj u v` means that some edge links `u` and `v` using two distinct incidences. -/
def Adj (G : IncidenceHypergraph ν ι ε) (u v : ν) : Prop :=
  ∃ e, G.IsLink e u v

lemma adj_iff_exists_incidence [Nonempty ε] [Nonempty ν] : G.Adj u v ↔
    ∃ i j : I(G), i ≠ j ∧ G.edgeMap i = G.edgeMap j ∧ G.attach i = u ∧ G.attach j = v := by
  simp only [Adj, isLink_iff_exists_incidence, ne_eq, exists_and_left, ↓existsAndEq, true_and,
    Subtype.exists, exists_and_right, Subtype.mk.injEq, exists_prop]
  grind

@[symm]
protected lemma Adj.symm (h : G.Adj u v) : G.Adj v u :=
  ⟨_, h.choose_spec.symm⟩

instance : Std.Symm G.Adj where
  symm _ _ := Adj.symm

lemma adj_comm (u v : ν) : G.Adj u v ↔ G.Adj v u :=
  ⟨.symm, .symm⟩

@[grind →]
lemma Adj.left_mem (h : G.Adj u v) : u ∈ V(G) :=
  h.choose_spec.left_mem

@[grind →]
lemma Adj.right_mem (h : G.Adj u v) : v ∈ V(G) :=
  h.symm.left_mem

lemma IsLink.adj (h : G.IsLink e u v) : G.Adj u v :=
  ⟨e, h⟩

lemma adj_iff_exists_subset_endSet_of_ne (huv : u ≠ v) : G.Adj u v ↔ ∃ e, {u, v} ⊆ G.endSet e := by
  simp only [Adj, isLink_iff_subset_endSet_of_ne huv]

@[simp]
lemma not_adj_of_notMem_vertexSet (hu : u ∉ V(G)) : ¬ G.Adj u v :=
  mt Adj.left_mem hu

@[simp]
lemma not_adj_of_notMem_vertexSet_right (hv : v ∉ V(G)) : ¬ G.Adj u v :=
  mt Adj.right_mem hv

/-! ### Extensionality -/

/-- Two incidence hypergraphs are equal if their active sets and incidence maps agree.
The maps are compared at the same ambient incidence, using membership proofs in the two sets. -/
@[ext]
protected lemma ext (hV : V(G) = V(H)) (hI : I(G) = I(H)) (hE : E(G) = E(H))
    (hEdge : ∀ (i : ι) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)), G.edgeMap' ⟨i, hiG⟩ = H.edgeMap' ⟨i, hiH⟩)
    (hAttach : ∀ (i : ι) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)),
      G.attach' ⟨i, hiG⟩ = H.attach' ⟨i, hiH⟩) : G = H := by
  cases G with | mk vertexSet incidenceSet edgeSet edgeMap edgeMap_mem attach attach_mem =>
  cases H with | mk vertexSet' incidenceSet' edgeSet' edgeMap' edgeMap_mem' attach' attach_mem' =>
  cases hV
  cases hI
  cases hE
  obtain rfl : edgeMap = edgeMap' := funext fun i ↦ hEdge i i.property i.property
  obtain rfl : attach = attach' := funext fun i ↦ hAttach i i.property i.property
  rfl

end IncidenceHypergraph
