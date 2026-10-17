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

This module defines `HypergraphLike` and its general incidence API for graph representations such
as `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `HypergraphLike`: records the vertices, edges, and incidences of a graph-like
  structure, with supplied edge and endpoint maps and source and target relations.
* `HypergraphLike.Link G e u v`: a specified source-to-target traversal of `e` from `u` to `v`,
  retaining its two distinct incidences.
* `HypergraphLike.IsLink G e u v`: the existence of such a link, defined as
  `Nonempty (Link G e u v)`.
* `HypergraphLike.Adj G u v`: the existence of an edge linking `u` to `v`.
* `HypergraphLike.edgeFiber` and `HypergraphLike.vertexFiber`: the incidences belonging
  to an edge or vertex.
* `HypergraphLike.incVerts` and `HypergraphLike.incEdges`: the vertices of an edge and the edges at
  a vertex, forgetting incidence multiplicity and orientation.

## Notation

In the `HypergraphLike` scope:
* `u ~[G] v` means `Adj G u v`.
* `u ~[G; e] v` means `IsLink G e u v`.

Both relations follow the order from source to target and need not be symmetric.

## Implementation notes

`HypergraphLike` abstracts a graph-like structure using separate types for vertices, incidences, and
edges. It uses incidence hypergraph definition, a span of incidences to edges and vertices,
generalized to also include directional information of whether an incidence is a source or target.

Incidence hypergraphs are more general than graphs or hypergraphs represented by set systems.
They allow any number of incidences between an edge and a vertex, and distinct edges with the same
incident vertices. The fields `IsSource` and `IsTarget` orient the incidences. Every incidence
is either a source or a target or both. Incidences that are sources but not targets, or targets but
not sources, are used to model directed edges. Incidences that are both sources and targets are
used to model undirected edges.

Links require two *distinct* incidences of an edge, one source and one target. This separates loops
(an edge with two incidences to the same vertex) and a dangling edge (an edge with one incidence
with a vertex). `Link G e u v` retains the chosen incidence data, while `IsLink G e u v` only
remembers the existence of a link. Adjacency is then the existence of an edge linking two vertices.
Both relations are derived from the incidence data and cannot be overridden by instances.

`HypergraphLike` uses ambient types for vertex, edge, and incidence labels. For `G : Gr`, the sets
`V(G)`, `E(G)`, and `I(G)` specify which labels are vertices, edges, and incidences of `G`.
The maps `edgeMap' G` and `attach' G` act on the subtype `I(G)`. Prefer the total maps `edgeMap G`
and `attach G` when the respective edge or vertex label type is nonempty. They agree with the
primed maps on `I(G)` and return arbitrary values on inputs outside `I(G)`. -/

@[expose] public section

open Set Function

/-- `HypergraphLike` abstracts types of graph-like structures using separate types for vertex,
incidence, and edge labels.

Consider a type `Gr` that models a graph-like structure. For `G : Gr`, `V(G)`, `E(G)`, and `I(G)`
specify the vertices, edges, and incidences present in `G`. You can view the elements of,
say, `ν : Type*` as all possible labels for vertices and only those in `V(G)` are the labels
actively being used in the given graph-like structure.
The maps `edgeMap' G` and `attach' G` assign an edge and endpoint to each incidence in `G`.
`IsSource` and `IsTarget` orient the incidences. The derived relations `IsLink G e u v` and
`Adj G u v` use two distinct incidences of one edge, with a source at `u` and a target at `v`. -/
class HypergraphLike (ν ι ε : outParam Type*) (Gr : Type*) where
  /-- The set of vertices present in a graph-like structure. -/
  verts (G : Gr) : Set ν
  /-- The set of edges present in a graph-like structure. -/
  edges (G : Gr) : Set ε
  /-- The set of incidences used by a graph-like structure. -/
  incs (G : Gr) : Set ι
  /-- Assigns an edge in `edges G` to each incidence in `incs G`, without a nonemptiness assumption.
  Prefer `HypergraphLike.edgeMap` which is a map from arbitrary incidence labels to edge labels. -/
  edgeMap' (G : Gr) (i : incs G) : edges G
  /-- Assigns a vertex in `verts G` to each incidence in `incs G`, with no nonemptiness assumption.
  Prefer `HypergraphLike.attach` which is a map from arbitrary incidence labels to vertex labels. -/
  attach' (G : Gr) (i : incs G) : verts G
  /-- The predicate whether an incidence is a source. -/
  IsSource (G : Gr) (i : ι) : Prop
  /-- The predicate whether an incidence is a target. -/
  IsTarget (G : Gr) (i : ι) : Prop
  /-- An incidence is used exactly when it is a source or target. -/
  mem_incs_iff ⦃G i⦄ : i ∈ incs G ↔ IsSource G i ∨ IsTarget G i

initialize_simps_projections HypergraphLike (as_prefix verts, as_prefix edges, as_prefix incs,
  IsSource → isSource, as_prefix isSource, IsTarget → isTarget, as_prefix isTarget)

namespace HypergraphLike

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

@[inherit_doc incs]
scoped notation "I(" G ")" => incs G

@[inherit_doc edges]
scoped notation "E(" G ")" => edges G

variable {V I E Gr : Type*} {G : Gr} [HypergraphLike V I E Gr] {u u' v v' w : V} {i j : I} {e f : E}

lemma IsSource.mem_incs (h : IsSource G i) : i ∈ I(G) := mem_incs_iff.mpr (Or.inl h)

lemma IsTarget.mem_incs (h : IsTarget G i) : i ∈ I(G) := mem_incs_iff.mpr (Or.inr h)

/-- A link from `u` to `v` through `e`, retaining its ordered pair of distinct incidences. -/
@[ext]
structure Link (G : Gr) (e : E) (u v : V) where
  /-- The source incidence of the link. -/
  source : I
  /-- The target incidence of the link. -/
  target : I
  /-- The two incidences are distinct, even when the attached vertices coincide. -/
  source_ne_target : source ≠ target
  /-- `source` is a valid source incidence. -/
  isSource_source : IsSource G source
  /-- `target` is a valid target incidence. -/
  isTarget_target : IsTarget G target
  /-- The source incidence belongs to the traversed edge. -/
  edgeMap'_source : edgeMap' G ⟨source, isSource_source.mem_incs⟩ = e
  /-- The target incidence belongs to the traversed edge. -/
  edgeMap'_target : edgeMap' G ⟨target, isTarget_target.mem_incs⟩ = e
  /-- The source incidence is attached to the first vertex. -/
  attach'_source : attach' G ⟨source, isSource_source.mem_incs⟩ = u
  /-- The target incidence is attached to the second vertex. -/
  attach'_target : attach' G ⟨target, isTarget_target.mem_incs⟩ = v

/-- `IsLink G e u v` means that a link from `u` to `v` through `e` exists. -/
def IsLink (G : Gr) (e : E) (u v : V) : Prop := Nonempty (Link G e u v)

/-- Two vertices are adjacent if some edge links the first to the second. -/
def Adj (G : Gr) (u v : V) : Prop := ∃ e, IsLink G e u v

@[inherit_doc Adj]
scoped notation:50 u:50 " ~[" G "] " v:50 => Adj G u v

@[inherit_doc IsLink]
scoped notation:50 u:50 " ~[" G "; " e "] " v:50 => IsLink G e u v

section HypergraphLike

/-! ### Incidence maps -/

lemma incs_eq_empty_of_verts_eq_empty (hV : V(G) = ∅) : I(G) = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun i hi ↦ by simpa [hV] using (attach' G ⟨i, hi⟩).property

lemma incs_eq_empty_of_edges_eq_empty (hE : E(G) = ∅) : I(G) = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun i hi ↦ by simpa [hE] using (edgeMap' G ⟨i, hi⟩).property

lemma verts_nonempty_of_incs_nonempty (hI : I(G).Nonempty) : V(G).Nonempty := by
  obtain ⟨i, hi⟩ := hI
  exact ⟨_, (attach' G ⟨i, hi⟩).property⟩

lemma edges_nonempty_of_incs_nonempty (hI : I(G).Nonempty) : E(G).Nonempty := by
  obtain ⟨i, hi⟩ := hI
  exact ⟨_, (edgeMap' G ⟨i, hi⟩).property⟩

open Classical in
/-- The vertex attached to an incidence, with an arbitrary value outside `I(G)`.
Unlike `HypergraphLike.attach'`, this takes arbitrary incidence labels and returns vertex labels,
requiring the vertex type to be nonempty. -/
noncomputable def attach [Nonempty V] (G : Gr) (i : I) : V :=
  if hi : i ∈ I(G) then attach' G ⟨i, hi⟩ else Classical.arbitrary V

open Classical in
/-- The edge of an incidence, with an arbitrary value outside `I(G)`.
Unlike `HypergraphLike.edgeMap'`, this takes arbitrary incidence labels and returns edge labels,
requiring the edge type to be nonempty. -/
noncomputable def edgeMap [Nonempty E] (G : Gr) (i : I) : E :=
  if hi : i ∈ I(G) then edgeMap' G ⟨i, hi⟩ else Classical.arbitrary E

@[simp]
lemma val_attach' [Nonempty V] (i : I(G)) : (attach' G i : V) = attach G (i : I) := by
  simp [attach]

@[simp]
lemma val_edgeMap' [Nonempty E] (i : I(G)) : (edgeMap' G i : E) = edgeMap G (i : I) := by
  simp [edgeMap]

lemma attach_mem_verts [Nonempty V] (hi : i ∈ I(G)) : attach G i ∈ V(G) := by
  simpa only [val_attach'] using (attach' G ⟨i, hi⟩).property

lemma edgeMap_mem_edges [Nonempty E] (hi : i ∈ I(G)) : edgeMap G i ∈ E(G) := by
  simpa only [val_edgeMap'] using (edgeMap' G ⟨i, hi⟩).property

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

@[simp]
lemma edgeFiber_of_notMem_edges (he : e ∉ E(G)) : edgeFiber G e = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hi ↦ he (mem_edges_of_mem_edgeFiber hi)

@[simp]
lemma vertexFiber_of_notMem_verts (hv : v ∉ V(G)) : vertexFiber G v = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hi ↦ hv (mem_verts_of_mem_vertexFiber hi)

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

@[simp]
lemma Link.edgeMap_source [Nonempty E] (l : Link G e u v) : edgeMap G l.source = e := by
  simpa using l.edgeMap'_source

@[simp]
lemma Link.edgeMap_target [Nonempty E] (l : Link G e u v) : edgeMap G l.target = e := by
  simpa using l.edgeMap'_target

@[simp]
lemma Link.attach_source [Nonempty V] (l : Link G e u v) : attach G l.source = u := by
  simpa using l.attach'_source

@[simp]
lemma Link.attach_target [Nonempty V] (l : Link G e u v) : attach G l.target = v := by
  simpa using l.attach'_target

/-- Forgetting the chosen incidences of a link. -/
lemma Link.isLink (l : Link G e u v) : u ~[G; e] v := ⟨l⟩

lemma Link.edge_mem_edgeSet (l : Link G e u v) : e ∈ E(G) :=
  l.edgeMap'_source ▸ (edgeMap' G ⟨l.source, l.isSource_source.mem_incs⟩).property

lemma Link.left_mem_vertexSet (l : Link G e u v) : u ∈ V(G) :=
  l.attach'_source ▸ (attach' G ⟨l.source, l.isSource_source.mem_incs⟩).property

lemma Link.right_mem_vertexSet (l : Link G e u v) : v ∈ V(G) :=
  l.attach'_target ▸ (attach' G ⟨l.target, l.isTarget_target.mem_incs⟩).property

lemma IsLink.edge_mem_edgeSet (h : u ~[G; e] v) : e ∈ E(G) :=
  h.elim (·.edge_mem_edgeSet)

lemma IsLink.left_mem_vertexSet (h : u ~[G; e] v) : u ∈ V(G) :=
  h.elim (·.left_mem_vertexSet)

lemma IsLink.right_mem_vertexSet (h : u ~[G; e] v) : v ∈ V(G) :=
  h.elim (·.right_mem_vertexSet)

@[grind →]
lemma IsLink.adj (h : u ~[G; e] v) : u ~[G] v := ⟨e, h⟩

@[grind →]
lemma Adj.left_mem_vertexSet (h : u ~[G] v) : u ∈ V(G) :=
  h.elim fun _ h ↦ h.left_mem_vertexSet

@[grind →]
lemma Adj.right_mem_vertexSet (h : u ~[G] v) : v ∈ V(G) :=
  h.elim fun _ h ↦ h.right_mem_vertexSet

@[simp]
lemma not_isLink_of_notMem_edges (he : e ∉ E(G)) : ¬ u ~[G; e] v := mt IsLink.edge_mem_edgeSet he

@[simp]
lemma not_adj_of_left_notMem_verts (hu : u ∉ V(G)) : ¬ u ~[G] v := mt Adj.left_mem_vertexSet hu

@[simp]
lemma not_adj_of_right_notMem_verts (hv : v ∉ V(G)) : ¬ u ~[G] v := mt Adj.right_mem_vertexSet hv

lemma isLink_iff_exists_incidence [Nonempty V] [Nonempty E] :
    u ~[G; e] v ↔
      ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ edgeMap G i = e ∧ edgeMap G j = e ∧
        attach G i = u ∧ attach G j = v := by
  refine ⟨fun ⟨l⟩ ↦ ⟨l.source, l.target, l.source_ne_target, l.isSource_source, l.isTarget_target,
    by simp⟩, ?_⟩
  rintro ⟨i, j, hne, hs, ht, he, rfl, rfl, rfl⟩
  refine ⟨⟨i, j, hne, hs, ht, ?_, ?_, ?_, ?_⟩⟩ <;> simp [he]

lemma isLink_attach [Nonempty V] [Nonempty E] (hs : IsSource G i) (ht : IsTarget G j) (hij : i ≠ j)
    (he : edgeMap G i = edgeMap G j) : attach G i ~[G; edgeMap G i] attach G j :=
  isLink_iff_exists_incidence.mpr ⟨i, j, hij, hs, ht, rfl, he.symm, rfl, rfl⟩

lemma adj_iff_exists_incidence [Nonempty V] [Nonempty E] :
    u ~[G] v ↔
      ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ edgeMap G i = edgeMap G j ∧
        attach G i = u ∧ attach G j = v := by
  simp only [Adj, isLink_iff_exists_incidence]
  exact ⟨fun ⟨e, i, j, hij, hs, ht, he, hf, hu, hv⟩ ↦ ⟨i, j, hij, hs, ht, he.trans hf.symm, hu, hv⟩,
    fun ⟨i, j, hij, hs, ht, he, hu, hv⟩ ↦ ⟨edgeMap G i, i, j, hij, hs, ht, rfl, he.symm, hu, hv⟩⟩

/-! ### Incident vertices and edges -/

/-- The set of vertices incident to an edge, as a source or a target. -/
def incVerts (G : Gr) (e : E) : Set V :=
  (fun i : I(G) ↦ (attach' G i : V)) '' {i | (edgeMap' G i : E) = e}

/-- The set of edges incident to a vertex, as a source or a target. -/
def incEdges (G : Gr) (v : V) : Set E :=
  (fun i : I(G) ↦ (edgeMap' G i : E)) '' {i | (attach' G i : V) = v}

@[simp, grind norm]
lemma mem_incEdges : e ∈ incEdges G v ↔ v ∈ incVerts G e := by
  simp [incEdges, incVerts, and_comm]

lemma incVerts_eq_image [Nonempty V] (G : Gr) : incVerts G e = attach G '' edgeFiber G e := by
  simp only [incVerts, edgeFiber, image_image, val_attach']

lemma incEdges_eq_image [Nonempty E] (G : Gr) : incEdges G v = edgeMap G '' vertexFiber G v := by
  simp only [incEdges, vertexFiber, image_image, val_edgeMap']

lemma mem_incVerts_iff_exists_incidence [Nonempty V] [Nonempty E] :
    v ∈ incVerts G e ↔ ∃ i, i ∈ I(G) ∧ edgeMap G i = e ∧ attach G i = v := by
  simp [incVerts_eq_image, and_assoc]

lemma mem_incEdges_iff_exists_incidence [Nonempty V] [Nonempty E] :
    e ∈ incEdges G v ↔ ∃ i, i ∈ I(G) ∧ attach G i = v ∧ edgeMap G i = e := by
  simp only [incEdges_eq_image, mem_image, mem_vertexFiber, and_assoc]

@[grind! ←]
lemma incVerts_subset_verts : incVerts G e ⊆ V(G) := by
  rintro v ⟨i, _, rfl⟩
  exact (attach' G i).property

@[grind! ←]
lemma incEdges_subset_edges : incEdges G v ⊆ E(G) := by
  rintro e ⟨i, _, rfl⟩
  exact (edgeMap' G i).property

@[grind →]
lemma mem_edges_of_mem_incVerts (h : v ∈ incVerts G e) : e ∈ E(G) :=
  incEdges_subset_edges (mem_incEdges.mpr h)

lemma mem_verts_of_mem_incEdges (h : e ∈ incEdges G v) : v ∈ V(G) :=
  incVerts_subset_verts (mem_incEdges.mp h)

@[simp, grind →]
lemma incVerts_of_notMem_edges (he : e ∉ E(G)) : incVerts G e = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hv ↦ he (mem_edges_of_mem_incVerts hv)

@[simp, grind →]
lemma incEdges_of_notMem_verts (hv : v ∉ V(G)) : incEdges G v = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ he ↦ hv (mem_verts_of_mem_incEdges he)

-- Emptiness and nonemptiness simplify to the incidence fibers, removing the endpoint/edge image.
@[simp]
lemma incVerts_eq_empty : incVerts G e = ∅ ↔ edgeFiber G e = ∅ := by
  simp [incVerts, edgeFiber]

@[simp]
lemma incEdges_eq_empty : incEdges G v = ∅ ↔ vertexFiber G v = ∅ := by
  simp [incEdges, vertexFiber]

@[simp]
lemma incVerts_nonempty : (incVerts G e).Nonempty ↔ (edgeFiber G e).Nonempty := by
  simp [incVerts, edgeFiber]

@[simp]
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
  obtain ⟨l⟩ := h
  exact ⟨⟨l.source, l.isSource_source.mem_incs⟩, l.edgeMap'_source, l.attach'_source⟩

@[grind →]
lemma IsLink.right_mem_incVerts (h : u ~[G; e] v) : v ∈ incVerts G e := by
  obtain ⟨l⟩ := h
  exact ⟨⟨l.target, l.isTarget_target.mem_incs⟩, l.edgeMap'_target, l.attach'_target⟩

lemma IsLink.mem_incEdges_left (h : u ~[G; e] v) : e ∈ incEdges G u :=
  mem_incEdges.mpr h.left_mem_incVerts

lemma IsLink.mem_incEdges_right (h : u ~[G; e] v) : e ∈ incEdges G v :=
  mem_incEdges.mpr h.right_mem_incVerts

end HypergraphLike

end HypergraphLike
