/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Data.Set.Card.Arithmetic

/-!
# An incidence interface for graph-like structures

This module defines `HyperGraphLike` and its general incidence API for graph representations such
as `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `HyperGraphLike`: records the vertices, edges, and incidence identifiers of a graph-like
  structure, with supplied edge and endpoint maps and source, target, link, and adjacency relations.
* `HyperGraphLike.edgeFiber` and `HyperGraphLike.vertexFiber`: the active incidence labels belonging
  to an edge or vertex.
* `HyperGraphLike.incVerts` and `HyperGraphLike.toEdges`: the vertices of an edge and the edges at
  a vertex, forgetting incidence multiplicity and orientation.
* `HyperGraphLike.degree` and `HyperGraphLike.order`: count incidences at a vertex or edge in `ℕ∞`.
* `HyperGraphLike.IsUniform` and `HyperGraphLike.IsRegular`: constant edge order and vertex degree.

## Implementation notes

Links and adjacency respect source and target roles and need not be symmetric. A link uses two
distinct incidence identifiers, including when its endpoints coincide. This separates loops (an edge
with two incidences to the same vertex) and a dangling edge (an edge with one incidence with a
vertex).

The maps in the definition of `HyperGraphLike` act on active subtypes. `edgeMap` and `attach` give
ambient values under the corresponding `Nonempty` assumptions, by sending an arbitrary value outside
the active incidence set.
-/

@[expose] public section

open Set Function

/-- `HyperGraphLike` abstracts a graph-like structure using separate types for vertices, incidence
identifiers, and edges.

Consider a type that models a graph-like structure, `Gr`. For `G : Gr`, `verts G`, `edges G`, and
`incs G` specify the vertices, edges, and incidence identifiers present in `G`. The supplied maps
`toEdge G` and `toVert G` assign an edge and endpoint to each active incidence.
The ambient types may contain unused labels.
`IsSource` and `IsTarget` orient the incidences. The derived relations `IsLink G e u v` and
`Adj G u v` use two distinct incidences of one edge, with a source at `u` and a target at `v`. -/
class HyperGraphLike (V I E : outParam Type*) (Gr : Type*) where
  /-- The set of vertices present in a graph-like structure. -/
  verts : Gr → Set V
  /-- The set of edges present in a graph-like structure. -/
  edges : Gr → Set E
  /-- The set of incidence identifiers used by a graph-like structure. -/
  incs : Gr → Set I
  /-- The edge of an active incidence. -/
  toEdge : ∀ G, incs G → edges G
  /-- The endpoint of an active incidence. -/
  toVert : ∀ G, incs G → verts G
  /-- The predicate that marks an incidence as a source incidence. -/
  IsSource : Gr → I → Prop
  /-- The predicate that marks an incidence as a target incidence. -/
  IsTarget : Gr → I → Prop
  /-- An incidence identifier is used exactly when it is marked as a source or target. -/
  mem_incs_iff ⦃G i⦄ : i ∈ incs G ↔ IsSource G i ∨ IsTarget G i
  -- Link and adjacency may be overridden for definitional agreement with a concrete representation.
  -- The accompanying fields require each override to agree with its default.
  /-- `IsLink G e u v` means that `e` has distinct source and target incidences at `u` and `v`. -/
  IsLink : Gr → E → V → V → Prop := fun G e u v ↦ ∃ i j : incs G, i ≠ j ∧
    IsSource G i.val ∧ IsTarget G j.val ∧ (toEdge G i).val = e ∧ (toVert G i).val = u ∧
    (toEdge G j).val = e ∧ (toVert G j).val = v
  /-- Characterizes `IsLink` using the supplied edge and endpoint maps of active incidences. -/
  isLink_iff ⦃G e u v⦄ : IsLink G e u v ↔ ∃ i j : incs G, i ≠ j ∧
    IsSource G i.val ∧ IsTarget G j.val ∧ (toEdge G i).val = e ∧ (toVert G i).val = u ∧
    (toEdge G j).val = e ∧ (toVert G j).val = v := by grind
  /-- `Adj G u v` means that some edge links `u` to `v`. -/
  Adj : Gr → V → V → Prop := fun G u v ↦ ∃ e, IsLink G e u v
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

variable {V I E Gr : Type*} {G : Gr} [HyperGraphLike V I E Gr] {u u' v v' w : V} {i j : I} {e f : E}

section HyperGraphLike

/-! ### Incidence maps -/

lemma IsSource.mem (h : IsSource G i) : i ∈ I(G) := mem_incs_iff.mpr (Or.inl h)

lemma IsTarget.mem (h : IsTarget G i) : i ∈ I(G) := mem_incs_iff.mpr (Or.inr h)

lemma incs_eq_empty_of_verts_eq_empty (hV : V(G) = ∅) : I(G) = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun i hi ↦ by simpa [hV] using (toVert G ⟨i, hi⟩).property

lemma incs_eq_empty_of_edges_eq_empty (hE : E(G) = ∅) : I(G) = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun i hi ↦ by simpa [hE] using (toEdge G ⟨i, hi⟩).property

open Classical in
/-- The vertex attached to an incidence, with an arbitrary value outside `I(G)`. -/
noncomputable def attach [Nonempty V] (G : Gr) (i : I) : V :=
  if hi : i ∈ I(G) then toVert G ⟨i, hi⟩ else Classical.arbitrary V

open Classical in
/-- The edge of an incidence, with an arbitrary value outside `I(G)`. -/
noncomputable def edgeMap [Nonempty E] (G : Gr) (i : I) : E :=
  if hi : i ∈ I(G) then toEdge G ⟨i, hi⟩ else Classical.arbitrary E

@[simp]
lemma toVert_eq_attach [Nonempty V] (i : I(G)) : (toVert G i : V) = attach G (i : I) := by
  simp [attach]

@[simp]
lemma toEdge_eq_edgeMap [Nonempty E] (i : I(G)) : (toEdge G i : E) = edgeMap G (i : I) := by
  simp [edgeMap]

lemma attach_mem [Nonempty V] (hi : i ∈ I(G)) : attach G i ∈ V(G) := by
  simpa only [toVert_eq_attach] using (toVert G ⟨i, hi⟩).property

lemma edgeMap_mem [Nonempty E] (hi : i ∈ I(G)) : edgeMap G i ∈ E(G) := by
  simpa only [toEdge_eq_edgeMap] using (toEdge G ⟨i, hi⟩).property

/-! ### Incidence fibers -/

/-- The active incidence labels belonging to an edge. -/
def edgeFiber (G : Gr) (e : E) : Set I :=
  Subtype.val '' {i : I(G) | (toEdge G i : E) = e}

/-- The active incidence labels attached to a vertex. -/
def vertexFiber (G : Gr) (v : V) : Set I :=
  Subtype.val '' {i : I(G) | (toVert G i : V) = v}

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
  exact (toEdge G j).property

lemma mem_verts_of_mem_vertexFiber (hi : i ∈ vertexFiber G v) : v ∈ V(G) := by
  obtain ⟨j, rfl, _⟩ := hi
  exact (toVert G j).property

lemma pairwise_disjoint_edgeFiber (G : Gr) : Pairwise (Disjoint on edgeFiber G) := by
  intro e f hef
  exact (disjoint_image_iff Subtype.val_injective).mpr
    (pairwise_disjoint_fiber (fun i : I(G) ↦ (toEdge G i : E)) hef)

lemma pairwise_disjoint_vertexFiber (G : Gr) : Pairwise (Disjoint on vertexFiber G) := by
  intro v w hvw
  exact (disjoint_image_iff Subtype.val_injective).mpr
    (pairwise_disjoint_fiber (fun i : I(G) ↦ (toVert G i : V)) hvw)

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

lemma adj_iff : Adj G u v ↔ ∃ e i j, i ≠ j ∧ IsSource G i.val ∧ IsTarget G j.val ∧
    (toEdge G i).val = e ∧ (toVert G i).val = u ∧ (toEdge G j).val = e ∧
    (toVert G j).val = v := by
  simp only [adj_iff', isLink_iff]

@[grind →]
lemma IsLink.edge_mem (h : IsLink G e u v) : e ∈ E(G) := by
  obtain ⟨i, _, _, _, _, rfl, _⟩ := isLink_iff.mp h
  exact (toEdge G i).property

@[grind →]
lemma IsLink.left_mem (h : IsLink G e u v) : u ∈ V(G) := by
  obtain ⟨i, _, _, _, _, _, rfl, _⟩ := isLink_iff.mp h
  exact (toVert G i).property

@[grind →]
lemma IsLink.right_mem (h : IsLink G e u v) : v ∈ V(G) := by
  obtain ⟨_, j, _, _, _, _, _, _, rfl⟩ := isLink_iff.mp h
  exact (toVert G j).property

@[grind →]
lemma IsLink.adj (h : IsLink G e u v) : Adj G u v := adj_iff'.mpr ⟨e, h⟩

@[grind →]
lemma Adj.left_mem (h : Adj G u v) : u ∈ V(G) := by
  obtain ⟨_, h⟩ := adj_iff'.mp h
  exact h.left_mem

@[grind →]
lemma Adj.right_mem (h : Adj G u v) : v ∈ V(G) := by
  obtain ⟨_, h⟩ := adj_iff'.mp h
  exact h.right_mem

@[simp]
lemma not_isLink_of_notMem_edges (he : e ∉ E(G)) : ¬ IsLink G e u v := mt IsLink.edge_mem he

@[simp]
lemma not_adj_of_notMem_verts (hu : u ∉ V(G)) : ¬ Adj G u v := mt Adj.left_mem hu

@[simp]
lemma not_adj_of_notMem_verts_right (hv : v ∉ V(G)) : ¬ Adj G u v := mt Adj.right_mem hv

lemma isLink_iff_exists_incidence [Nonempty V] [Nonempty E] : IsLink G e u v ↔
    ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ edgeMap G i = e ∧ edgeMap G j = e ∧
    attach G i = u ∧ attach G j = v := by
  simp only [isLink_iff, toEdge_eq_edgeMap, toVert_eq_attach]
  exact ⟨fun ⟨i, j, hij, hs, ht, he, hu, hf, hv⟩ ↦
    ⟨i, j, fun h ↦ hij (Subtype.ext h), hs, ht, he, hf, hu, hv⟩,
    fun ⟨i, j, hij, hs, ht, he, hf, hu, hv⟩ ↦
    ⟨⟨i, hs.mem⟩, ⟨j, ht.mem⟩, fun h ↦ hij (congrArg Subtype.val h), hs, ht, he, hu, hf, hv⟩⟩

lemma isLink_attach [Nonempty V] [Nonempty E] (hs : IsSource G i) (ht : IsTarget G j) (hij : i ≠ j)
    (he : edgeMap G i = edgeMap G j) : IsLink G (edgeMap G i) (attach G i) (attach G j) :=
  isLink_iff_exists_incidence.mpr ⟨i, j, hij, hs, ht, rfl, he.symm, rfl, rfl⟩

lemma adj_iff_exists_incidence [Nonempty V] [Nonempty E] : Adj G u v ↔
    ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ edgeMap G i = edgeMap G j ∧
    attach G i = u ∧ attach G j = v := by
  simp only [adj_iff', isLink_iff_exists_incidence]
  exact ⟨fun ⟨e, i, j, hij, hs, ht, he, hf, hu, hv⟩ ↦ ⟨i, j, hij, hs, ht, he.trans hf.symm, hu, hv⟩,
    fun ⟨i, j, hij, hs, ht, he, hu, hv⟩ ↦ ⟨edgeMap G i, i, j, hij, hs, ht, rfl, he.symm, hu, hv⟩⟩

/-! ### Incident vertices and edges -/

/-- The set of vertices incident to an edge, forgetting incidence multiplicity and orientation. -/
def incVerts (G : Gr) (e : E) : Set V :=
  (fun i : I(G) ↦ (toVert G i : V)) '' {i | (toEdge G i : E) = e}

/-- The set of edges incident to a vertex, forgetting incidence multiplicity and orientation. -/
def toEdges (G : Gr) (v : V) : Set E :=
  (fun i : I(G) ↦ (toEdge G i : E)) '' {i | (toVert G i : V) = v}

@[simp]
lemma mem_toEdges : e ∈ toEdges G v ↔ v ∈ incVerts G e := by
  simp [toEdges, incVerts, and_comm]

lemma incVerts_eq_image [Nonempty V] (G : Gr) : incVerts G e = attach G '' edgeFiber G e := by
  simp only [incVerts, edgeFiber, image_image, toVert_eq_attach]

lemma toEdges_eq_image [Nonempty E] (G : Gr) : toEdges G v = edgeMap G '' vertexFiber G v := by
  simp only [toEdges, vertexFiber, image_image, toEdge_eq_edgeMap]

lemma mem_incVerts_iff_exists_incidence [Nonempty V] [Nonempty E] :
    v ∈ incVerts G e ↔ ∃ i, i ∈ I(G) ∧ edgeMap G i = e ∧ attach G i = v := by
  simp [incVerts_eq_image, and_assoc]

lemma mem_toEdges_iff_exists_incidence [Nonempty V] [Nonempty E] :
    e ∈ toEdges G v ↔ ∃ i, i ∈ I(G) ∧ attach G i = v ∧ edgeMap G i = e := by
  rw [toEdges_eq_image]
  simp only [mem_image, mem_vertexFiber, and_assoc]

lemma incVerts_subset_verts : incVerts G e ⊆ V(G) := by
  rintro v ⟨i, _, rfl⟩
  exact (toVert G i).property

lemma toEdges_subset_edges : toEdges G v ⊆ E(G) := by
  rintro e ⟨i, _, rfl⟩
  exact (toEdge G i).property

lemma mem_edges_of_mem_incVerts (h : v ∈ incVerts G e) : e ∈ E(G) :=
  toEdges_subset_edges (mem_toEdges.mpr h)

lemma mem_verts_of_mem_toEdges (h : e ∈ toEdges G v) : v ∈ V(G) :=
  incVerts_subset_verts (mem_toEdges.mp h)

@[simp]
lemma incVerts_of_notMem_edges (he : e ∉ E(G)) : incVerts G e = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hv ↦ he (mem_edges_of_mem_incVerts hv)

@[simp]
lemma toEdges_of_notMem_verts (hv : v ∉ V(G)) : toEdges G v = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ he ↦ hv (mem_verts_of_mem_toEdges he)

lemma incVerts_eq_empty : incVerts G e = ∅ ↔ edgeFiber G e = ∅ := by
  simp [incVerts, edgeFiber]

lemma toEdges_eq_empty : toEdges G v = ∅ ↔ vertexFiber G v = ∅ := by
  simp [toEdges, vertexFiber]

lemma incVerts_nonempty : (incVerts G e).Nonempty ↔ (edgeFiber G e).Nonempty := by
  simp [incVerts, edgeFiber]

lemma toEdges_nonempty : (toEdges G v).Nonempty ↔ (vertexFiber G v).Nonempty := by
  simp [toEdges, vertexFiber]

lemma attach_mem_incVerts [Nonempty V] [Nonempty E] (hi : i ∈ I(G)) :
    attach G i ∈ incVerts G (edgeMap G i) :=
  mem_incVerts_iff_exists_incidence.mpr ⟨i, hi, rfl, rfl⟩

lemma edgeMap_mem_toEdges [Nonempty V] [Nonempty E] (hi : i ∈ I(G)) :
    edgeMap G i ∈ toEdges G (attach G i) :=
  mem_toEdges.mpr (attach_mem_incVerts hi)

@[grind →]
lemma IsLink.left_mem_incVerts (h : IsLink G e u v) : u ∈ incVerts G e := by
  obtain ⟨i, _, _, _, _, he, hu, _⟩ := isLink_iff.mp h
  exact ⟨i, he, hu⟩

@[grind →]
lemma IsLink.right_mem_incVerts (h : IsLink G e u v) : v ∈ incVerts G e := by
  obtain ⟨_, j, _, _, _, _, _, he, hv⟩ := isLink_iff.mp h
  exact ⟨j, he, hv⟩

lemma IsLink.pair_subset_incVerts (h : IsLink G e u v) : {u, v} ⊆ incVerts G e :=
  Set.pair_subset_iff.mpr ⟨h.left_mem_incVerts, h.right_mem_incVerts⟩

@[grind →]
lemma IsLink.mem_toEdges_left (h : IsLink G e u v) : e ∈ toEdges G u :=
  mem_toEdges.mpr h.left_mem_incVerts

@[grind →]
lemma IsLink.mem_toEdges_right (h : IsLink G e u v) : e ∈ toEdges G v :=
  mem_toEdges.mpr h.right_mem_incVerts

/-! ### Degree and order -/

/-- The number of active incidences of an edge, with value `⊤` for an infinite fiber. -/
noncomputable def order (G : Gr) (e : E) : ℕ∞ := {i : I(G) | (toEdge G i : E) = e}.encard

/-- The number of active incidences attached to a vertex, with value `⊤` for an infinite fiber. -/
noncomputable def degree (G : Gr) (v : V) : ℕ∞ := {i : I(G) | (toVert G i : V) = v}.encard

lemma order_eq_encard_edgeFiber (G : Gr) : order G e = (edgeFiber G e).encard :=
  (Subtype.val_injective.encard_image _).symm

lemma degree_eq_encard_vertexFiber (G : Gr) : degree G v = (vertexFiber G v).encard :=
  (Subtype.val_injective.encard_image _).symm

lemma degree_eq_zero [Nonempty V] : degree G v = 0 ↔ ∀ i ∈ I(G), attach G i ≠ v := by
  simp [degree_eq_encard_vertexFiber, eq_empty_iff_forall_notMem]

lemma degree_pos [Nonempty V] : 0 < degree G v ↔ ∃ i ∈ I(G), attach G i = v := by
  simp [degree_eq_encard_vertexFiber, Set.Nonempty]

lemma degree_eq_zero_iff_toEdges_eq_empty : degree G v = 0 ↔ toEdges G v = ∅ := by
  simp [degree_eq_encard_vertexFiber, toEdges_eq_empty]

lemma degree_pos_iff_nonempty_toEdges : 0 < degree G v ↔ (toEdges G v).Nonempty := by
  simp [degree_eq_encard_vertexFiber, toEdges_nonempty]

@[simp]
lemma degree_of_notMem_verts (hv : v ∉ V(G)) : degree G v = 0 :=
  degree_eq_zero_iff_toEdges_eq_empty.mpr (toEdges_of_notMem_verts hv)

lemma degree_attach_pos [Nonempty V] (hi : i ∈ I(G)) : 0 < degree G (attach G i) :=
  degree_pos.mpr ⟨i, hi, rfl⟩

lemma mem_verts_of_degree_pos (h : 0 < degree G v) : v ∈ V(G) := by
  obtain ⟨e, he⟩ := degree_pos_iff_nonempty_toEdges.mp h
  exact mem_verts_of_mem_toEdges he

lemma degree_le_encard_incs : degree G v ≤ I(G).encard :=
  (degree_eq_encard_vertexFiber G).trans_le (encard_mono vertexFiber_subset_incs)

lemma degree_lt_top_iff : degree G v < ⊤ ↔ (vertexFiber G v).Finite := by
  rw [degree_eq_encard_vertexFiber, encard_lt_top_iff]

lemma degree_eq_top_iff : degree G v = ⊤ ↔ (vertexFiber G v).Infinite := by
  rw [degree_eq_encard_vertexFiber, encard_eq_top_iff]

lemma degree_lt_top_of_finite (hI : I(G).Finite) : degree G v < ⊤ :=
  degree_lt_top_iff.mpr (hI.subset vertexFiber_subset_incs)

lemma order_eq_zero : order G e = 0 ↔ incVerts G e = ∅ := by
  simp [order_eq_encard_edgeFiber, incVerts_eq_empty]

lemma order_pos : 0 < order G e ↔ (incVerts G e).Nonempty := by
  simp [order_eq_encard_edgeFiber, incVerts_nonempty]

@[simp]
lemma order_of_notMem_edges (he : e ∉ E(G)) : order G e = 0 :=
  order_eq_zero.mpr (incVerts_of_notMem_edges he)

lemma order_edgeMap_pos [Nonempty E] (hi : i ∈ I(G)) : 0 < order G (edgeMap G i) := by
  rw [order_eq_encard_edgeFiber, encard_pos]
  exact ⟨i, mem_edgeFiber.mpr ⟨hi, rfl⟩⟩

lemma mem_edges_of_order_pos (h : 0 < order G e) : e ∈ E(G) := by
  obtain ⟨v, hv⟩ := order_pos.mp h
  exact mem_edges_of_mem_incVerts hv

lemma order_le_encard_incs : order G e ≤ I(G).encard :=
  (order_eq_encard_edgeFiber G).trans_le (encard_mono edgeFiber_subset_incs)

lemma order_lt_top_iff : order G e < ⊤ ↔ (edgeFiber G e).Finite := by
  rw [order_eq_encard_edgeFiber, encard_lt_top_iff]

lemma order_eq_top_iff : order G e = ⊤ ↔ (edgeFiber G e).Infinite := by
  rw [order_eq_encard_edgeFiber, encard_eq_top_iff]

lemma order_lt_top_of_finite (hI : I(G).Finite) : order G e < ⊤ :=
  order_lt_top_iff.mpr (hI.subset edgeFiber_subset_incs)

lemma encard_incVerts_le_order : (incVerts G e).encard ≤ order G e := encard_image_le _ _

lemma encard_toEdges_le_degree : (toEdges G v).encard ≤ degree G v := encard_image_le _ _

lemma degree_pos_iff_exists_mem_incVerts : 0 < degree G v ↔ ∃ e, v ∈ incVerts G e := by
  simp only [degree_pos_iff_nonempty_toEdges, Set.Nonempty, mem_toEdges]

lemma degree_eq_zero_iff_forall_notMem_incVerts : degree G v = 0 ↔ ∀ e, v ∉ incVerts G e := by
  simp only [degree_eq_zero_iff_toEdges_eq_empty, eq_empty_iff_forall_notMem, mem_toEdges]

lemma degree_eq_zero_of_incs_eq_empty (hI : I(G) = ∅) : degree G v = 0 := by
  simpa [hI] using degree_le_encard_incs (G := G) (v := v)

lemma order_eq_zero_of_incs_eq_empty (hI : I(G) = ∅) : order G e = 0 := by
  simpa [hI] using order_le_encard_incs (G := G) (e := e)

/-! ### Counting incidences -/

/-- Summing degrees over a finite active vertex set counts all incidences. This is true without
finiteness assumption but requires importing topology here. -/
lemma sum_degree (G : Gr) [Fintype V(G)] : ∑ v : V(G), degree G (v : V) = I(G).encard := by
  simpa only [iUnion_subtype, biUnion_vertexFiber, ← degree_eq_encard_vertexFiber,
    finsum_eq_sum_of_fintype] using (encard_iUnion_of_finite (ι := V(G))
      ((pairwise_disjoint_vertexFiber G).comp_of_injective Subtype.val_injective)).symm

/-- Summing orders over a finite active edge set counts all incidences. This is true without
finiteness assumption but requires importing topology here. -/
lemma sum_order (G : Gr) [Fintype E(G)] : ∑ e : E(G), order G (e : E) = I(G).encard := by
  simpa only [iUnion_subtype, biUnion_edgeFiber, ← order_eq_encard_edgeFiber,
    finsum_eq_sum_of_fintype] using (encard_iUnion_of_finite (ι := E(G))
      ((pairwise_disjoint_edgeFiber G).comp_of_injective Subtype.val_injective)).symm

/-- The degree sum equals the edge order sum when both active indexing sets are finite. This is true
without finiteness assumption but requires importing topology here. -/
lemma sum_degree_eq_sum_order (G : Gr) [Fintype V(G)] [Fintype E(G)] :
    ∑ v : V(G), degree G (v : V) = ∑ e : E(G), order G (e : E) :=
  (sum_degree G).trans (sum_order G).symm

/-! ### Uniformity and regularity -/

/-- Every active edge has order `k`, counting incidences with multiplicity.
For `k = ⊤`, every active edge has infinitely many incidences. -/
def IsUniform (G : Gr) (k : ℕ∞) : Prop := ∀ {e}, e ∈ E(G) → order G e = k

/-- Every active vertex has degree `k`, counting incidences with multiplicity.
For `k = ⊤`, every active vertex has infinitely many incidences. -/
def IsRegular (G : Gr) (k : ℕ∞) : Prop := ∀ {v}, v ∈ V(G) → degree G v = k

variable {k l : ℕ∞}

lemma IsUniform.eq_of_nonempty (hk : IsUniform G k) (hl : IsUniform G l) (hE : E(G).Nonempty) :
    k = l := by
  obtain ⟨e, he⟩ := hE
  exact (hk he).symm.trans (hl he)

lemma IsRegular.eq_of_nonempty (hk : IsRegular G k) (hl : IsRegular G l) (hV : V(G).Nonempty) :
    k = l := by
  obtain ⟨v, hv⟩ := hV
  exact (hk hv).symm.trans (hl hv)

lemma isUniform_of_edges_eq_empty (hE : E(G) = ∅) : IsUniform G k := by
  simp [IsUniform, hE]

lemma isRegular_of_verts_eq_empty (hV : V(G) = ∅) : IsRegular G k := by
  simp [IsRegular, hV]

@[simp]
lemma isUniform_zero : IsUniform G 0 ↔ I(G) = ∅ := by
  simp only [IsUniform, order_eq_encard_edgeFiber, encard_eq_zero, ← iUnion_eq_empty,
    biUnion_edgeFiber]

@[simp]
lemma isRegular_zero : IsRegular G 0 ↔ I(G) = ∅ := by
  simp only [IsRegular, degree_eq_encard_vertexFiber, encard_eq_zero, ← iUnion_eq_empty,
    biUnion_vertexFiber]

lemma IsLink.one_lt_order (h : IsLink G e u v) : 1 < order G e := by
  obtain ⟨i, j, hij, _, _, hi, _, hj, _⟩ := isLink_iff.mp h
  exact one_lt_encard_iff.mpr ⟨i, j, hi, hj, hij⟩

lemma edgeMap_preimage_singleton_injOn [Nonempty E] (h : ∀ e ∈ E(G), order G e ≠ 0) :
    InjOn (fun e ↦ edgeMap G ⁻¹' {e}) E(G) := by
  intro e he f hf hef
  obtain ⟨i, hi⟩ := encard_ne_zero.mp (order_eq_encard_edgeFiber G ▸ h e he)
  have hi := (mem_edgeFiber.mp hi).2
  exact hi.symm.trans ((Set.ext_iff.mp hef i).mp hi)

end HyperGraphLike

end HyperGraphLike
