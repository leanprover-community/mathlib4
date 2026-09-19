/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.IncidenceGraph.Basic
public import Mathlib.Data.Set.Notation
public import Mathlib.Topology.PrimitiveLink

/-!
# Drawings of incidence graphs

This file defines geometric drawings of incidence graphs using primitive links for edge ranges.

## Main definitions

* `IncidenceGraph.Drawing`: a placement of vertices and geometric edge ranges.
* `IncidenceGraph.Drawing.support`: the support of the whole drawing.
* `IncidenceGraph.Drawing.edgeBoundary`: the images of the ends of an edge.
* `IncidenceGraph.Drawing.edgeInterior`: the edge range with its boundary removed.
* `IncidenceGraph.Drawing.IsNoncrossing`: distinct edge interiors are disjoint.
-/

@[expose] public section

open Set
open scoped Set.Notation

namespace IncidenceGraph

variable {ν ι ε : Type*} {X : Type*} [TopologicalSpace X] {G : IncidenceGraph ν ι ε}
  {e f : E(G)} {u v : V(G)}

/-- Geometric drawing of a graph. Crossings between distinct edges are allowed. -/
structure Drawing (G : IncidenceGraph ν ι ε) (X : Type*) [TopologicalSpace X] where
  /-- Injective placement of active graph vertices. -/
  vertex : V(G) ↪ X
  /-- Geometric support of each labelled graph edge. -/
  edgeRange : E(G) → Set X
  /-- Every `IsLink` presentation of an edge supplies the same primitive-link geometry. -/
  edge_isPrimitiveLink : ∀ {e : E(G)} {u v : V(G)}, G.IsLink e.1 u.1 v.1 →
    IsPrimitiveLink (edgeRange e) (vertex u) (vertex v)
  /-- The only graph vertices on an edge range are vertices incident with that edge. -/
  inc_of_vertex_mem_edgeRange :
    ∀ (e : E(G)) (v : V(G)), vertex v ∈ edgeRange e → v.val ∈ G.endSet e

/-- A primitive edge range given in one orientation has the orientation supplied by any other
`IsLink` proof for the same edge. -/
lemma isPrimitiveLink_of_isLink {e : E(G)} {u v x y : V(G)} {f : V(G) → X}
    {L : Set X} (huv : G.IsLink e.1 u.1 v.1) (hxy : G.IsLink e.1 x.1 y.1)
    (hL : IsPrimitiveLink L (f u) (f v)) : IsPrimitiveLink L (f x) (f y) := by
  obtain ⟨hux, hvy⟩ | ⟨huy, hvx⟩ := huv.eq_and_eq_or_eq_and_eq hxy
  · simpa [Subtype.ext hux, Subtype.ext hvy] using hL
  simpa [Subtype.ext huy, Subtype.ext hvx] using hL.symm

namespace Drawing

variable {D D' : Drawing G X}

/-- Image of the graph vertices. -/
def vertexImage (D : Drawing G X) : Set X :=
  range D.vertex

/-- Geometric support of the whole drawing. -/
def support (D : Drawing G X) : Set X :=
  D.vertexImage ∪ ⋃ e : E(G), D.edgeRange e

/-- Images of the combinatorial ends of an edge. -/
def edgeBoundary (D : Drawing G X) (e : E(G)) : Set X :=
  D.vertex '' (V(G) ↓∩ G.endSet e)

/-- Image of the open combinatorial edge cell. This is not ambient topological interior. -/
def edgeInterior (D : Drawing G X) (e : E(G)) : Set X :=
  D.edgeRange e \ D.edgeBoundary e

/-- A drawing is noncrossing when distinct open edge cells are pairwise disjoint. -/
def IsNoncrossing (D : Drawing G X) : Prop :=
  ∀ ⦃e f : E(G)⦄, e ≠ f → Disjoint (D.edgeInterior e) (D.edgeInterior f)

/-- Points lying in the interiors of at least two distinct labelled edges. -/
def crossingSet (D : Drawing G X) : Set X :=
  {x | ∃ e f : E(G), e ≠ f ∧ x ∈ D.edgeInterior e ∧ x ∈ D.edgeInterior f}

/-- Build an intrinsic drawing from vertex positions and geometric edge ranges.

It suffices to prove primitive-link geometry in one orientation for each edge; the resulting drawing
supports every orientation supplied by an `IsLink` proof. Crossings between distinct edge ranges are
allowed and are governed separately by `IsNoncrossing`. -/
@[simps]
def ofEdgeRanges (vertex : V(G) ↪ X) (edgeRange : E(G) → Set X)
    (edge_isPrimitiveLink : ∀ e : E(G), ∃ u v : V(G), G.IsLink e.1 u.1 v.1 ∧
      IsPrimitiveLink (edgeRange e) (vertex u) (vertex v)) (inc_of_vertex_mem_edgeRange :
    ∀ (e : E(G)) (v : V(G)), vertex v ∈ edgeRange e → v.val ∈ G.endSet e) : Drawing G X where
  vertex := vertex
  edgeRange := edgeRange
  edge_isPrimitiveLink hxy := by
    obtain ⟨u, v, huv, hL⟩ := edge_isPrimitiveLink _
    exact isPrimitiveLink_of_isLink huv hxy hL
  inc_of_vertex_mem_edgeRange := inc_of_vertex_mem_edgeRange

@[ext]
theorem ext (hv : ∀ v, D.vertex v = D'.vertex v) (he : ∀ e, D.edgeRange e = D'.edgeRange e) :
    D = D' := by
  cases D
  cases D'
  simp only [Drawing.mk.injEq]
  exact ⟨DFunLike.ext _ _ hv, funext he⟩

@[simp]
lemma vertex_mem_vertexImage (v : V(G)) : D.vertex v ∈ D.vertexImage :=
  mem_range_self v

lemma vertexImage_subset_support : D.vertexImage ⊆ D.support :=
  subset_union_left

lemma vertex_mem_support (v : V(G)) : D.vertex v ∈ D.support :=
  vertexImage_subset_support <| D.vertex_mem_vertexImage v

lemma edgeRange_subset_support (e : E(G)) : D.edgeRange e ⊆ D.support :=
  subset_union_of_subset_right (subset_iUnion _ e) _

lemma edgeBoundary_subset_vertexImage (e : E(G)) : D.edgeBoundary e ⊆ D.vertexImage :=
  image_subset_range _ _

/-- Exact graph-vertex incidence on an edge range. Only the forward implication is structure data;
the reverse implication follows from primitive-link endpoint membership. -/
@[simp]
lemma vertex_mem_edgeRange_iff (e : E(G)) (v : V(G)) :
    D.vertex v ∈ D.edgeRange e ↔ v.val ∈ G.endSet e := by
  refine ⟨D.inc_of_vertex_mem_edgeRange e v, fun ⟨i, hi, hv⟩ ↦ ?_⟩
  have h : G.IsLink e.val v.val (G.attach' (G.other' i)) := by
    simpa only [show G.edgeMap' i = e.val from hi, hv] using isLink_attach_other' (G := G) i
  exact (D.edge_isPrimitiveLink (v := ⟨_, G.attach'_mem (G.other' i)⟩) h).left_mem

lemma edgeBoundary_subset_edgeRange (e : E(G)) : D.edgeBoundary e ⊆ D.edgeRange e := by
  rintro x ⟨v, hv, rfl⟩
  rwa [vertex_mem_edgeRange_iff]

lemma edgeRange_inter_vertexImage (e : E(G)) :
    D.edgeRange e ∩ D.vertexImage = D.edgeBoundary e := by
  ext x
  constructor
  · rintro ⟨hx, ⟨v, -, rfl⟩⟩
    exact ⟨v, (D.vertex_mem_edgeRange_iff e v).mp hx, rfl⟩
  rintro ⟨v, hv, rfl⟩
  exact ⟨(D.vertex_mem_edgeRange_iff e v).mpr hv, D.vertex_mem_vertexImage v⟩

lemma edgeInterior_disjoint_vertexImage (e : E(G)) : Disjoint (D.edgeInterior e) D.vertexImage := by
  refine disjoint_left.mpr fun x hxI hxV ↦ hxI.2 ?_
  rw [← D.edgeRange_inter_vertexImage e]
  exact ⟨hxI.1, hxV⟩

lemma edgeInterior_subset_edgeRange (e : E(G)) : D.edgeInterior e ⊆ D.edgeRange e :=
  sdiff_subset

lemma edgeInterior_subset_support (e : E(G)) : D.edgeInterior e ⊆ D.support :=
  (D.edgeInterior_subset_edgeRange e).trans (D.edgeRange_subset_support e)

lemma edgeBoundary_eq_of_isLink (h : G.IsLink e.1 u.1 v.1) :
    D.edgeBoundary e = {D.vertex u, D.vertex v} := by
  ext z
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨w, ⟨i, hi, hw⟩, rfl⟩
    have hwlink : G.IsLink e.val w.val (G.attach' (G.other' i)) := by
      simpa only [show G.edgeMap' i = e.val from hi, hw] using isLink_attach_other' (G := G) i
    grind [hwlink.left_eq_or_eq h]
  obtain rfl | rfl : z = D.vertex u ∨ z = D.vertex v := by
    simpa [mem_insert_iff, mem_singleton_iff] using hz
  · exact ⟨u, h.left_mem_endSet, rfl⟩
  exact ⟨v, h.right_mem_endSet, rfl⟩

lemma edgeInterior_eq_of_isLink (h : G.IsLink e.1 u.1 v.1) :
    D.edgeInterior e = D.edgeRange e \ {D.vertex u, D.vertex v} := by
  rw [edgeInterior, D.edgeBoundary_eq_of_isLink h]

/-- Every closed set containing the open cell of an edge also contains its ends, because the ends
are limits of interior points. Nothing polygonal and nothing two-dimensional is involved. -/
lemma edgeBoundary_subset_of_edgeInterior_subset (e : E(G)) {S : Set X} (hS : IsClosed S)
    (hsub : D.edgeInterior e ⊆ S) : D.edgeBoundary e ⊆ S := by
  obtain ⟨x, y, h⟩ := edge_mem_iff_exists_isLink.mp e.2
  replace h : G.IsLink e.1 (⟨x, h.left_mem⟩ : V(G)).1 (⟨y, h.right_mem⟩ : V(G)).1 := h
  rw [D.edgeInterior_eq_of_isLink h] at hsub
  obtain ⟨hx, hy⟩ := (D.edge_isPrimitiveLink h).endpoints_mem_of_diff_subset hS hsub
  rw [D.edgeBoundary_eq_of_isLink h]
  exact insert_subset hx (singleton_subset_iff.mpr hy)

lemma edgeRange_nonempty (e : E(G)) : (D.edgeRange e).Nonempty := by
  obtain ⟨x, y, hxy⟩ := edge_mem_iff_exists_isLink.mp e.2
  exact (D.edge_isPrimitiveLink (u := ⟨x, hxy.left_mem⟩) (v := ⟨y, hxy.right_mem⟩) hxy).nonempty

lemma edgeRange_isCompact (e : E(G)) : IsCompact (D.edgeRange e) := by
  obtain ⟨x, y, hxy⟩ := edge_mem_iff_exists_isLink.mp e.2
  exact (D.edge_isPrimitiveLink (u := ⟨x, hxy.left_mem⟩) (v := ⟨y, hxy.right_mem⟩) hxy).isCompact

lemma edgeRange_isPathConnected (e : E(G)) : IsPathConnected (D.edgeRange e) := by
  obtain ⟨x, y, hxy⟩ := edge_mem_iff_exists_isLink.mp e.2
  exact D.edge_isPrimitiveLink (u := ⟨x, hxy.left_mem⟩) (v := ⟨y, hxy.right_mem⟩) hxy
    |>.isPathConnected

lemma edgeRange_isConnected (e : E(G)) : IsConnected (D.edgeRange e) :=
  (D.edgeRange_isPathConnected e).isConnected

lemma edgeInterior_nonempty (e : E(G)) : (D.edgeInterior e).Nonempty := by
  obtain ⟨x, y, hxy⟩ := edge_mem_iff_exists_isLink.mp e.2
  rw [D.edgeInterior_eq_of_isLink (u := ⟨x, hxy.left_mem⟩) (v := ⟨y, hxy.right_mem⟩) hxy]
  exact D.edge_isPrimitiveLink (u := ⟨x, hxy.left_mem⟩) (v := ⟨y, hxy.right_mem⟩) hxy
    |>.diff_endpoints_nonempty

lemma edgeInterior_isPathConnected (e : E(G)) : IsPathConnected (D.edgeInterior e) := by
  obtain ⟨x, y, hxy⟩ := edge_mem_iff_exists_isLink.mp e.2
  rw [D.edgeInterior_eq_of_isLink (u := ⟨x, hxy.left_mem⟩) (v := ⟨y, hxy.right_mem⟩) hxy]
  exact D.edge_isPrimitiveLink (u := ⟨x, hxy.left_mem⟩) (v := ⟨y, hxy.right_mem⟩) hxy
    |>.isPathConnected_diff_endpoints

lemma edgeInterior_isConnected (e : E(G)) : IsConnected (D.edgeInterior e) :=
  (D.edgeInterior_isPathConnected e).isConnected

lemma crossingSet_eq_iUnion :
    D.crossingSet = ⋃ e : E(G), ⋃ f : E(G), ⋃ _ : e ≠ f, (D.edgeInterior e ∩ D.edgeInterior f) := by
  ext x
  simp only [mem_iUnion, crossingSet, mem_ofPred]
  exact ⟨fun ⟨e, f, hef, hxe, hxf⟩ ↦ ⟨e, f, hef, hxe, hxf⟩,
    fun ⟨e, f, hef, hx⟩ ↦ ⟨e, f, hef, hx.1, hx.2⟩⟩

lemma isNoncrossing_iff_crossingSet_eq_empty : D.IsNoncrossing ↔ D.crossingSet = ∅ := by
  refine ⟨fun hD ↦ eq_empty_of_forall_notMem fun x ⟨e, f, hef, hxe, hxf⟩ ↦ ?_,
    fun hL e f hef ↦ disjoint_left.mpr fun x hxe hxf ↦ ?_⟩
  · exact (hD hef).notMem_of_mem_left hxe hxf
  have hx : x ∈ D.crossingSet := ⟨e, f, hef, hxe, hxf⟩
  rwa [hL] at hx

lemma IsNoncrossing.crossingSet_eq_empty (hD : D.IsNoncrossing) : D.crossingSet = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, _, hef, hxe, hxf⟩ ↦ (hD hef).notMem_of_mem_left hxe hxf

/-- Under noncrossingness, two distinct edge ranges meet exactly in their common graph endpoints. -/
lemma IsNoncrossing.edgeRange_inter_edgeRange_of_ne (hD : D.IsNoncrossing) (hef : e ≠ f) :
    D.edgeRange e ∩ D.edgeRange f = D.edgeBoundary e ∩ D.edgeBoundary f := by
  refine subset_antisymm (fun x ⟨hxe, hxf⟩ ↦ ?_) fun x ⟨hbe, hbf⟩ ↦
    ⟨D.edgeBoundary_subset_edgeRange e hbe, D.edgeBoundary_subset_edgeRange f hbf⟩
  by_cases hbe : x ∈ D.edgeBoundary e
  · exact ⟨hbe, D.edgeRange_inter_vertexImage f ▸ ⟨hxf, D.edgeBoundary_subset_vertexImage e hbe⟩⟩
  have hbf : x ∈ D.edgeBoundary f :=
    by_contra fun hbf ↦ (disjoint_left.mp (hD hef)) ⟨hxe, hbe⟩ ⟨hxf, hbf⟩
  exact ⟨D.edgeRange_inter_vertexImage e ▸ ⟨hxe, D.edgeBoundary_subset_vertexImage f hbf⟩, hbf⟩

lemma vertexImage_isCompact [Finite V(G)] : IsCompact D.vertexImage :=
  (finite_range (D.vertex : V(G) → X)).isCompact

lemma support_isCompact [Finite V(G)] [Finite E(G)] : IsCompact D.support :=
  D.vertexImage_isCompact.union (isCompact_iUnion D.edgeRange_isCompact)

lemma support_isClosed [Finite V(G)] [Finite E(G)] [T2Space X] : IsClosed D.support :=
  D.support_isCompact.isClosed

end IncidenceGraph.Drawing
