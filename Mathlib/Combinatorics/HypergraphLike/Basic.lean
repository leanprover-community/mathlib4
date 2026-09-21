/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# General interface for graph-like structures

This module defines `HyperGraphLike` and its general incidence API for graph representations such
as `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `HyperGraphLike`: records the vertices, edges, and incidences of a graph-like
  structure, with supplied edge and endpoint maps and source, target, link, and adjacency relations.
* `HyperGraphLike.edgeFiber` and `HyperGraphLike.vertexFiber`: the active incidence labels belonging
  to an edge or vertex.
* `HyperGraphLike.incVerts` and `HyperGraphLike.incEdges`: the vertices of an edge and the edges at
  a vertex, forgetting incidence multiplicity and orientation.

## Notation

In the `HyperGraphLike` scope:
* `u ~[G] v` means `Adj G u v`.
* `u ~[G; e] v` means `IsLink G e u v`.

Both relations follow the order from source to target and need not be symmetric.

## Implementation notes

`HypergraphLike` abstracts a graph-like structure using separate types for vertices, incidences, and
edges. It uses incidence hypergraph definition, a span of incidences to edges and vertices,
generalized to also include directional information of whether an incidence is a source or target.

Incidence hypergraphs are more general than graphs or definitions of hypergraph based on
set-systems. Incidence hypergraphs allow for arbitrary number of incidences of an edge and a vertex,
and arbitrary number of edges between two vertices. It also has good categorical properties. Two
additional fields, `IsSource` and `IsTarget`, are used to orient the incidences. Every incidence
is either a source or a target or both. Strictly source and target incidences are used to model
directed edges and source & target incidences are used to model undirected edges.

Links require two *distinct* incidences of an edge, one source and one target. This separates loops
(an edge with two incidences to the same vertex) and a dangling edge (an edge with one incidence
with a vertex). Adjacency is then simply the existence of a link between two vertices.

Rather than directly using the given types, `HyperGraphLike` has fields for the set of vertices,
edges, and incidences, and only those in the sets are treated as part of the graph-like
structure. You can view the elements of, say, `ν : Type*` as all possible labels for vertices and
only those in `V(G)` are the labels actively being used in the graph-like structure. The maps in
the definition of `HyperGraphLike` act on subtypes of `incs G` and people are discouraged from using
them directly. Instead, `edgeMap` and `attach` are defined on all incidence type under the
corresponding `Nonempty` assumptions, by sending an arbitrary value outside the active incidence
set. -/

@[expose] public section

open Set Function

/-- `HyperGraphLike` abstracts types of graph-like structures using separate types for vertices,
incidences, and edges.

Consider a type `Gr` that models a graph-like structure. For `G : Gr`, `V(G)`, `E(G)`, and `I(G)`
specify the vertices, edges, and incidences present in `G`. You can view the elements of,
say, `ν : Type*` as all possible labels for vertices and only those in `V(G)` are the labels
actively being used in the given graph-like structure.
The maps `edgeMap' G` and `attach' G` assign an edge and endpoint to each incidence in `G`.
`IsSource` and `IsTarget` orient the incidences. The derived relations `IsLink G e u v` and
`Adj G u v` use two distinct incidences of one edge, with a source at `u` and a target at `v`. -/
class HyperGraphLike (ν ι ε : outParam Type*) (Gr : Type*) where
  /-- The set of vertices present in a graph-like structure. -/
  verts (G : Gr) : Set ν
  /-- The set of edges present in a graph-like structure. -/
  edges (G : Gr) : Set ε
  /-- The set of incidence used by a graph-like structure. -/
  incs (G : Gr) : Set ι
  /-- Each incidence is assigned an edge. -/
  edgeMap' (G : Gr) (i : incs G) : edges G
  /-- Each incidence is assigned a vertex. -/
  attach' (G : Gr) (i : incs G) : verts G
  /-- The predicate whether an incidence is a source. -/
  IsSource (G : Gr) (i : ι) : Prop
  /-- The predicate whether an incidence is a target. -/
  IsTarget (G : Gr) (i : ι) : Prop
  /-- An incidence is used exactly when it is a source or target. -/
  mem_incs_iff ⦃G i⦄ : i ∈ incs G ↔ IsSource G i ∨ IsTarget G i
  -- Link and adjacency may be overridden for definitional agreement with a concrete representation.
  -- The accompanying fields require each override to agree with its default.
  /-- `IsLink G e u v` means that `e` has distinct source and target incidences at `u` and `v`. -/
  IsLink (G : Gr) (e : ε) (u v : ν) : Prop := ∃ i j : incs G, i ≠ j ∧
    IsSource G i.val ∧ IsTarget G j.val ∧ (edgeMap' G i).val = e ∧ (attach' G i).val = u ∧
    (edgeMap' G j).val = e ∧ (attach' G j).val = v
  /-- Characterizes `IsLink` using the supplied edge and endpoint maps of active incidences. -/
  isLink_iff ⦃G e u v⦄ : IsLink G e u v ↔ ∃ i j : incs G, i ≠ j ∧
    IsSource G i.val ∧ IsTarget G j.val ∧ (edgeMap' G i).val = e ∧ (attach' G i).val = u ∧
    (edgeMap' G j).val = e ∧ (attach' G j).val = v := by grind
  /-- `Adj G u v` means that some edge links `u` to `v`. -/
  Adj (G : Gr) (u v : ν) : Prop := ∃ e, IsLink G e u v
  /-- Adjacency means that an edge links the two vertices. -/
  adj_iff' ⦃G u v⦄ : Adj G u v ↔ ∃ e, IsLink G e u v := by grind

initialize_simps_projections HyperGraphLike (as_prefix verts, as_prefix edges, as_prefix incs,
  IsSource → isSource, as_prefix isSource, IsTarget → isTarget, as_prefix isTarget,
  IsLink → isLink, as_prefix isLink, Adj → adj, as_prefix adj)

namespace HyperGraphLike

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

@[inherit_doc incs]
scoped notation "I(" G ")" => incs G

@[inherit_doc edges]
scoped notation "E(" G ")" => edges G

@[inherit_doc Adj]
scoped notation:50 u:50 " ~[" G "] " v:50 => Adj G u v

@[inherit_doc IsLink]
scoped notation:50 u:50 " ~[" G "; " e "] " v:50 => IsLink G e u v

variable {V I E Gr : Type*} {G : Gr} [HyperGraphLike V I E Gr] {u u' v v' w : V} {i j : I} {e f : E}

section HyperGraphLike

/-! ### Incidence maps -/

lemma IsSource.mem_incs (h : IsSource G i) : i ∈ I(G) := mem_incs_iff.mpr (Or.inl h)

lemma IsTarget.mem_incs (h : IsTarget G i) : i ∈ I(G) := mem_incs_iff.mpr (Or.inr h)

lemma incs_eq_empty_of_verts_eq_empty (hV : V(G) = ∅) : I(G) = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun i hi ↦ by simpa [hV] using (attach' G ⟨i, hi⟩).property

lemma incs_eq_empty_of_edges_eq_empty (hE : E(G) = ∅) : I(G) = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun i hi ↦ by simpa [hE] using (edgeMap' G ⟨i, hi⟩).property

open Classical in
/-- The vertex attached to an incidence, with an arbitrary value outside `I(G)`. -/
noncomputable def attach [Nonempty V] (G : Gr) (i : I) : V :=
  if hi : i ∈ I(G) then attach' G ⟨i, hi⟩ else Classical.arbitrary V

open Classical in
/-- The edge of an incidence, with an arbitrary value outside `I(G)`. -/
noncomputable def edgeMap [Nonempty E] (G : Gr) (i : I) : E :=
  if hi : i ∈ I(G) then edgeMap' G ⟨i, hi⟩ else Classical.arbitrary E

@[simp]
lemma val_attach'_eq_attach [Nonempty V] (i : I(G)) : (attach' G i : V) = attach G (i : I) := by
  simp [attach]

@[simp]
lemma val_edgeMap'_eq_edgeMap [Nonempty E] (i : I(G)) : (edgeMap' G i : E) = edgeMap G (i : I) := by
  simp [edgeMap]

lemma attach_mem_verts [Nonempty V] (hi : i ∈ I(G)) : attach G i ∈ V(G) := by
  simpa only [val_attach'_eq_attach] using (attach' G ⟨i, hi⟩).property

lemma edgeMap_mem_edges [Nonempty E] (hi : i ∈ I(G)) : edgeMap G i ∈ E(G) := by
  simpa only [val_edgeMap'_eq_edgeMap] using (edgeMap' G ⟨i, hi⟩).property

/-! ### Incidence fibers -/

/-- The incidence labels belonging to an edge. -/
def edgeFiber (G : Gr) (e : E) : Set I :=
  Subtype.val '' {i : I(G) | (edgeMap' G i : E) = e}

/-- The incidence labels attached to a vertex. -/
def vertexFiber (G : Gr) (v : V) : Set I :=
  Subtype.val '' {i : I(G) | (attach' G i : V) = v}

@[simp]
lemma mem_edgeFiber [Nonempty E] : i ∈ edgeFiber G e ↔ i ∈ I(G) ∧ edgeMap G i = e := by
  simp [edgeFiber, and_comm]

@[simp]
lemma mem_vertexFiber [Nonempty V] : i ∈ vertexFiber G v ↔ i ∈ I(G) ∧ attach G i = v := by
  simp [vertexFiber, and_comm]

lemma edgeFiber_eq_inter_preimage [Nonempty E] (G : Gr) :
    edgeFiber G e = I(G) ∩ edgeMap G ⁻¹' {e} := by
  ext i
  simp

lemma vertexFiber_eq_inter_preimage [Nonempty V] (G : Gr) :
    vertexFiber G v = I(G) ∩ attach G ⁻¹' {v} := by
  ext i
  simp

lemma edgeFiber_subset_incs : edgeFiber G e ⊆ I(G) :=
  image_subset_iff.mpr fun i _ ↦ i.property

lemma vertexFiber_subset_incs : vertexFiber G v ⊆ I(G) :=
  image_subset_iff.mpr fun i _ ↦ i.property

lemma mem_edges_of_mem_edgeFiber (hi : i ∈ edgeFiber G e) : e ∈ E(G) := by
  obtain ⟨j, rfl, _⟩ := hi
  exact (edgeMap' G j).property

lemma mem_verts_of_mem_vertexFiber (hi : i ∈ vertexFiber G v) : v ∈ V(G) := by
  obtain ⟨j, rfl, _⟩ := hi
  exact (attach' G j).property

lemma pairwise_disjoint_edgeFiber (G : Gr) : Pairwise (Disjoint on edgeFiber G) :=
  fun _ _ hef ↦ (disjoint_image_iff Subtype.val_injective).mpr
    (pairwise_disjoint_fiber (fun i : I(G) ↦ (edgeMap' G i : E)) hef)

lemma pairwise_disjoint_vertexFiber (G : Gr) : Pairwise (Disjoint on vertexFiber G) :=
  fun _ _ hvw ↦ (disjoint_image_iff Subtype.val_injective).mpr
    (pairwise_disjoint_fiber (fun i : I(G) ↦ (attach' G i : V)) hvw)

@[simp]
lemma iUnion_edgeFiber (G : Gr) : ⋃ e, edgeFiber G e = I(G) := by
  ext i
  simp [edgeFiber, exists_comm]

@[simp]
lemma iUnion_vertexFiber (G : Gr) : ⋃ v, vertexFiber G v = I(G) := by
  ext i
  simp [vertexFiber, exists_comm]

@[simp]
lemma biUnion_edgeFiber (G : Gr) : ⋃ e ∈ E(G), edgeFiber G e = I(G) := by
  ext i
  simp [edgeFiber]

@[simp]
lemma biUnion_vertexFiber (G : Gr) : ⋃ v ∈ V(G), vertexFiber G v = I(G) := by
  ext i
  simp [vertexFiber]

/-! ### Links and adjacency -/

@[grind →]
lemma IsLink.edge_mem_edgeSet (h : u ~[G; e] v) : e ∈ E(G) := by
  obtain ⟨i, _, _, _, _, rfl, _⟩ := isLink_iff.mp h
  exact (edgeMap' G i).property

@[grind →]
lemma IsLink.left_mem_vertexSet (h : u ~[G; e] v) : u ∈ V(G) := by
  obtain ⟨i, _, _, _, _, _, rfl, _⟩ := isLink_iff.mp h
  exact (attach' G i).property

@[grind →]
lemma IsLink.right_mem_vertexSet (h : u ~[G; e] v) : v ∈ V(G) := by
  obtain ⟨_, j, _, _, _, _, _, _, rfl⟩ := isLink_iff.mp h
  exact (attach' G j).property

@[grind →]
lemma IsLink.adj (h : u ~[G; e] v) : u ~[G] v := adj_iff'.mpr ⟨e, h⟩

@[grind →]
lemma Adj.left_mem_vertexSet (h : u ~[G] v) : u ∈ V(G) :=
  (adj_iff'.mp h).elim fun _ h ↦ h.left_mem_vertexSet

@[grind →]
lemma Adj.right_mem_vertexSet (h : u ~[G] v) : v ∈ V(G) :=
  (adj_iff'.mp h).elim fun _ h ↦ h.right_mem_vertexSet

@[simp]
lemma not_isLink_of_notMem_edges (he : e ∉ E(G)) : ¬ u ~[G; e] v := mt IsLink.edge_mem_edgeSet he

@[simp]
lemma not_adj_of_notMem_verts (hu : u ∉ V(G)) : ¬ u ~[G] v := mt Adj.left_mem_vertexSet hu

@[simp]
lemma not_adj_of_notMem_verts_right (hv : v ∉ V(G)) : ¬ u ~[G] v := mt Adj.right_mem_vertexSet hv

lemma isLink_iff_exists_incidence [Nonempty V] [Nonempty E] :
    u ~[G; e] v ↔
      ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ edgeMap G i = e ∧ edgeMap G j = e ∧
        attach G i = u ∧ attach G j = v := by
  simp only [isLink_iff, val_edgeMap'_eq_edgeMap, val_attach'_eq_attach]
  exact ⟨fun ⟨i, j, hij, hs, ht, he, hu, hf, hv⟩ ↦
    ⟨i, j, fun h ↦ hij (Subtype.ext h), hs, ht, he, hf, hu, hv⟩,
    fun ⟨i, j, hij, hs, ht, he, hf, hu, hv⟩ ↦
    ⟨⟨i, hs.mem_incs⟩, ⟨j, ht.mem_incs⟩, fun h ↦ hij (congrArg Subtype.val h),
      hs, ht, he, hu, hf, hv⟩⟩

lemma isLink_attach [Nonempty V] [Nonempty E] (hs : IsSource G i) (ht : IsTarget G j) (hij : i ≠ j)
    (he : edgeMap G i = edgeMap G j) : attach G i ~[G; edgeMap G i] attach G j :=
  isLink_iff_exists_incidence.mpr ⟨i, j, hij, hs, ht, rfl, he.symm, rfl, rfl⟩

lemma adj_iff_exists_incidence [Nonempty V] [Nonempty E] :
    u ~[G] v ↔
      ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ edgeMap G i = edgeMap G j ∧
        attach G i = u ∧ attach G j = v := by
  simp only [adj_iff', isLink_iff_exists_incidence]
  exact ⟨fun ⟨e, i, j, hij, hs, ht, he, hf, hu, hv⟩ ↦ ⟨i, j, hij, hs, ht, he.trans hf.symm, hu, hv⟩,
    fun ⟨i, j, hij, hs, ht, he, hu, hv⟩ ↦ ⟨edgeMap G i, i, j, hij, hs, ht, rfl, he.symm, hu, hv⟩⟩

/-! ### Incident vertices and edges -/

/-- The set of vertices incident to an edge, as a source or a target. -/
def incVerts (G : Gr) (e : E) : Set V :=
  (fun i : I(G) ↦ (attach' G i : V)) '' {i | (edgeMap' G i : E) = e}

/-- The set of edges incident to a vertex, as a source or a target. -/
def incEdges (G : Gr) (v : V) : Set E :=
  (fun i : I(G) ↦ (edgeMap' G i : E)) '' {i | (attach' G i : V) = v}

@[simp]
lemma mem_incEdges : e ∈ incEdges G v ↔ v ∈ incVerts G e := by
  simp [incEdges, incVerts, and_comm]

lemma incVerts_eq_image [Nonempty V] (G : Gr) : incVerts G e = attach G '' edgeFiber G e := by
  simp only [incVerts, edgeFiber, image_image, val_attach'_eq_attach]

lemma incEdges_eq_image [Nonempty E] (G : Gr) : incEdges G v = edgeMap G '' vertexFiber G v := by
  simp only [incEdges, vertexFiber, image_image, val_edgeMap'_eq_edgeMap]

lemma mem_incVerts_iff_exists_incidence [Nonempty V] [Nonempty E] :
    v ∈ incVerts G e ↔ ∃ i, i ∈ I(G) ∧ edgeMap G i = e ∧ attach G i = v := by
  simp [incVerts_eq_image, and_assoc]

lemma mem_incEdges_iff_exists_incidence [Nonempty V] [Nonempty E] :
    e ∈ incEdges G v ↔ ∃ i, i ∈ I(G) ∧ attach G i = v ∧ edgeMap G i = e := by
  simp only [incEdges_eq_image, mem_image, mem_vertexFiber, and_assoc]

lemma incVerts_subset_verts : incVerts G e ⊆ V(G) := by
  rintro v ⟨i, _, rfl⟩
  exact (attach' G i).property

lemma incEdges_subset_edges : incEdges G v ⊆ E(G) := by
  rintro e ⟨i, _, rfl⟩
  exact (edgeMap' G i).property

@[grind →]
lemma mem_edges_of_mem_incVerts (h : v ∈ incVerts G e) : e ∈ E(G) :=
  incEdges_subset_edges (mem_incEdges.mpr h)

@[grind →]
lemma mem_verts_of_mem_incEdges (h : e ∈ incEdges G v) : v ∈ V(G) :=
  incVerts_subset_verts (mem_incEdges.mp h)

@[simp]
lemma incVerts_of_notMem_edges (he : e ∉ E(G)) : incVerts G e = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hv ↦ he (mem_edges_of_mem_incVerts hv)

@[simp]
lemma incEdges_of_notMem_verts (hv : v ∉ V(G)) : incEdges G v = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ he ↦ hv (mem_verts_of_mem_incEdges he)

lemma incVerts_eq_empty : incVerts G e = ∅ ↔ edgeFiber G e = ∅ := by
  simp [incVerts, edgeFiber]

lemma incEdges_eq_empty : incEdges G v = ∅ ↔ vertexFiber G v = ∅ := by
  simp [incEdges, vertexFiber]

lemma incVerts_nonempty : (incVerts G e).Nonempty ↔ (edgeFiber G e).Nonempty := by
  simp [incVerts, edgeFiber]

lemma incEdges_nonempty : (incEdges G v).Nonempty ↔ (vertexFiber G v).Nonempty := by
  simp [incEdges, vertexFiber]

lemma attach_mem_incVerts [Nonempty V] [Nonempty E] (hi : i ∈ I(G)) :
    attach G i ∈ incVerts G (edgeMap G i) :=
  mem_incVerts_iff_exists_incidence.mpr ⟨i, hi, rfl, rfl⟩

lemma edgeMap_mem_incEdges [Nonempty V] [Nonempty E] (hi : i ∈ I(G)) :
    edgeMap G i ∈ incEdges G (attach G i) :=
  mem_incEdges.mpr (attach_mem_incVerts hi)

@[grind →]
lemma IsLink.left_mem_incVerts (h : u ~[G; e] v) : u ∈ incVerts G e := by
  obtain ⟨i, _, _, _, _, he, hu, _⟩ := isLink_iff.mp h
  exact ⟨i, he, hu⟩

@[grind →]
lemma IsLink.right_mem_incVerts (h : u ~[G; e] v) : v ∈ incVerts G e := by
  obtain ⟨_, j, _, _, _, _, _, he, hv⟩ := isLink_iff.mp h
  exact ⟨j, he, hv⟩

lemma IsLink.pair_subset_incVerts (h : u ~[G; e] v) : {u, v} ⊆ incVerts G e :=
  pair_subset_iff.mpr ⟨h.left_mem_incVerts, h.right_mem_incVerts⟩

@[grind →]
lemma IsLink.mem_incEdges_left (h : u ~[G; e] v) : e ∈ incEdges G u :=
  mem_incEdges.mpr h.left_mem_incVerts

@[grind →]
lemma IsLink.mem_incEdges_right (h : u ~[G; e] v) : e ∈ incEdges G v :=
  mem_incEdges.mpr h.right_mem_incVerts

end HyperGraphLike

end HyperGraphLike
