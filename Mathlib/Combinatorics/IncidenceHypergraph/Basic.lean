/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Set.Card.Arithmetic

/-!
# Incidence hypergraphs

This file defines hypergraphs with ambient vertex, incidence, and edge types. Each active
incidence has an associated edge and an attached vertex.

## Main definitions

* `IncidenceHypergraph`: the incidence hypergraph structure.
* `IncidenceHypergraph.IsLink`: two distinct incidences of an edge with specified attached vertices.
* `IncidenceHypergraph.endSet`: the vertices attached to incidences of an edge.
* `IncidenceHypergraph.Adj`: two vertices are joined by an `IsLink`.
* `IncidenceHypergraph.dual`: exchange vertices and edges while preserving incidence labels.
* `IncidenceHypergraph.degree`: the number of incidences attached to a vertex.
* `IncidenceHypergraph.order`: the number of incidences belonging to an edge.
* `IncidenceHypergraph.IsUniform`: all active edges have a specified order.
* `IncidenceHypergraph.IsRegular`: all active vertices have a specified degree.

## Implementation notes

The underlying mathematical data is a span of sets `V(G) ← I(G) → E(G)`, with maps induced by
`attach` and `edgeMap`. This is the span definition of a hypergraph described by
[nLab](https://ncatlab.org/nlab/show/hypergraph).

This is a quite permissive definition of a hypergraph, where there can be multiple incidences
between an edge and a vertex, and there could be isolated vertices and edges.

Degrees and edge orders count incidences with multiplicity and take values in `ℕ∞`. All infinite
fibers have count `⊤`, regardless of their cardinality. Duality exchanges degree with order and
regularity with uniformity.

## Notation

Within the `IncidenceHypergraph` scope, `V(G)`, `I(G)`, and `E(G)` denote the vertex, incidence,
and edge sets.
-/

@[expose] public section

variable {ν ι ε : Type*}

open Set Function

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
/-- The vertex attached to an incidence, with an arbitrary value outside `I(G)`. -/
noncomputable def attach [Nonempty ν] (G : IncidenceHypergraph ν ι ε) (i : ι) : ν :=
  if h : i ∈ I(G) then G.attach' ⟨i, h⟩ else Classical.arbitrary ν

lemma attach_mem [Nonempty ν] (hi : i ∈ I(G)) : attach G i ∈ V(G) := by
  simp [attach, hi]

@[simp]
lemma attach'_eq_attach [Nonempty ν] (i : I(G)) : G.attach' i = attach G i := by
  simp [attach]

open Classical in
/-- The edge associated with an incidence, with an arbitrary value outside `I(G)`. -/
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

lemma isLink_attach (hi : i ∈ I(G)) (hj : j ∈ I(G)) (hij : i ≠ j)
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
    G.dual.edgeMap i = G.attach i :=
  rfl

@[simp]
lemma attach_dual [Nonempty ε] (G : IncidenceHypergraph ν ι ε) (i : ι) :
    G.dual.attach i = G.edgeMap i :=
  rfl

@[simp]
lemma dual_dual (G : IncidenceHypergraph ν ι ε) : G.dual.dual = G :=
  rfl

@[simp]
lemma mem_endSet_dual : e ∈ G.dual.endSet v ↔ v ∈ G.endSet e :=
  ⟨fun ⟨i, hv, he⟩ ↦ ⟨i, he, hv⟩, fun ⟨i, he, hv⟩ ↦ ⟨i, hv, he⟩⟩

lemma dual_bijective : Bijective (dual : IncidenceHypergraph ν ι ε → _) :=
  ⟨fun _ _ h ↦ by simpa using congrArg dual h, fun G ↦ ⟨G.dual, G.dual_dual⟩⟩

@[simp]
lemma dual_inj : G.dual = H.dual ↔ G = H :=
  dual_bijective.injective.eq_iff

/-! ### Degree and order -/

/-- The number of incidences attached to a vertex, with value `⊤` for an infinite fiber.
Repeated incidences are counted separately. The degree is zero outside the active vertex set. -/
noncomputable def degree (G : IncidenceHypergraph ν ι ε) (v : ν) : ℕ∞ :=
  (G.attach' ⁻¹' {v}).encard

/-- The number of incidences belonging to an edge, with value `⊤` for an infinite fiber.
Repeated incidences are counted separately. The order is zero outside the active edge set. -/
noncomputable def order (G : IncidenceHypergraph ν ι ε) (e : ε) : ℕ∞ :=
  (G.edgeMap' ⁻¹' {e}).encard

@[simp]
lemma degree_dual (G : IncidenceHypergraph ν ι ε) (e : ε) : G.dual.degree e = G.order e :=
  rfl

@[simp]
lemma order_dual (G : IncidenceHypergraph ν ι ε) (v : ν) : G.dual.order v = G.degree v :=
  rfl

lemma degree_eq_zero [Nonempty ν] : G.degree v = 0 ↔ ∀ i ∈ I(G), G.attach i ≠ v := by
  simp [degree, Set.eq_empty_iff_forall_notMem]

lemma degree_pos [Nonempty ν] : 0 < G.degree v ↔ ∃ i ∈ I(G), G.attach i = v := by
  simp [degree, Set.Nonempty]

@[simp]
lemma degree_of_notMem_vertexSet (hv : v ∉ V(G)) : G.degree v = 0 := by
  rw [degree, encard_eq_zero, preimage_eq_empty_iff, disjoint_singleton_left]
  exact mt (G.range_attach'_subset ·) hv

lemma degree_attach_pos [Nonempty ν] (G : IncidenceHypergraph ν ι ε) (hi : i ∈ I(G)) :
    0 < G.degree (G.attach i) :=
  degree_pos.mpr ⟨i, hi, rfl⟩

lemma mem_vertexSet_of_degree_pos (h : 0 < G.degree v) : v ∈ V(G) := by
  rw [degree, encard_pos] at h
  obtain ⟨i, rfl⟩ := h
  exact G.attach'_mem i

lemma degree_le_encard_incidenceSet : G.degree v ≤ I(G).encard :=
  Set.encard_le_card

lemma degree_lt_top_of_finite (hI : I(G).Finite) : G.degree v < ⊤ :=
  degree_le_encard_incidenceSet.trans_lt hI.encard_lt_top

lemma order_eq_zero : G.order e = 0 ↔ G.endSet e = ∅ := by
  simp [order, endSet]

lemma order_pos : 0 < G.order e ↔ (G.endSet e).Nonempty := by
  simp [order, endSet]

@[simp]
lemma order_of_notMem_edgeSet (he : e ∉ E(G)) : G.order e = 0 :=
  degree_of_notMem_vertexSet (G := G.dual) he

lemma order_edgeMap'_pos (G : IncidenceHypergraph ν ι ε) (i : I(G)) :
    0 < G.order (G.edgeMap' i) := Set.encard_pos.mpr ⟨i, rfl⟩

lemma mem_edgeSet_of_order_pos (h : 0 < G.order e) : e ∈ E(G) :=
  mem_vertexSet_of_degree_pos (G := G.dual) h

lemma order_le_encard_incidenceSet : G.order e ≤ I(G).encard :=
  degree_le_encard_incidenceSet (G := G.dual)

lemma encard_endSet_le_order : (G.endSet e).encard ≤ G.order e :=
  Set.encard_image_le _ _

lemma degree_eq_zero_iff_forall_notMem_endSet : G.degree v = 0 ↔ ∀ e, v ∉ G.endSet e := by
  rw [← order_dual G v, order_eq_zero, Set.eq_empty_iff_forall_notMem]
  simp

/-- An edge has order greater than one exactly when it supports a link, possibly a loop. -/
lemma one_lt_order_iff : 1 < G.order e ↔ ∃ u v, G.IsLink e u v := by
  rw [order, Set.one_lt_encard_iff]
  constructor
  · rintro ⟨i, j, hi, hj, hij⟩
    exact ⟨G.attach' i, G.attach' j, i, j, hij, hi, hj, rfl, rfl⟩
  rintro ⟨u, v, i, j, hij, hi, hj, -, -⟩
  exact ⟨i, j, hi, hj, hij⟩

lemma IsLink.one_lt_order {u : ν} (h : G.IsLink e u v) : 1 < G.order e :=
  one_lt_order_iff.mpr ⟨u, v, h⟩

lemma degree_eq_zero_of_incidenceSet_eq_empty (hI : I(G) = ∅) : G.degree v = 0 :=
  Set.encard_eq_zero.mpr <| Set.eq_empty_iff_forall_notMem.mpr fun i ↦
    (Set.notMem_empty i.val (hI ▸ i.property)).elim

lemma order_eq_zero_of_incidenceSet_eq_empty (hI : I(G) = ∅) : G.order e = 0 :=
  degree_eq_zero_of_incidenceSet_eq_empty (G := G.dual) hI

/-! ### Counting incidences -/

/-- Summing degrees over a finite active vertex set counts all incidences. This is true without
finiteness assumption but requires importing topology here. -/
lemma sum_degree (G : IncidenceHypergraph ν ι ε) [Fintype V(G)] :
    ∑ v : V(G), G.degree v = I(G).encard := by
  have hUnion : ⋃ v : V(G), G.attach' ⁻¹' {v.val} = Set.univ := by
    ext i
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨⟨G.attach' i, G.attach'_mem i⟩, rfl⟩
  have hDisjoint :
      Pairwise fun v w : V(G) ↦ Disjoint (G.attach' ⁻¹' {v.val}) (G.attach' ⁻¹' {w.val}) :=
    fun v w hvw ↦  Set.disjoint_left.mpr fun i hv hw ↦ hvw (Subtype.ext (hv.symm.trans hw))
  simpa [hUnion, degree, Set.encard_univ, finsum_eq_sum_of_fintype] using
    (Set.encard_iUnion_of_finite hDisjoint).symm

/-- Summing orders over a finite active edge set counts all incidences. This is true without
finiteness assumption but requires importing topology here. -/
lemma sum_order (G : IncidenceHypergraph ν ι ε) [Fintype E(G)] :
    ∑ e : E(G), G.order e = I(G).encard := by
  let : Fintype V(G.dual) := ‹Fintype E(G)›
  exact G.dual.sum_degree

/-- The degree sum equals the edge order sum when both active indexing sets are finite. This is true
without finiteness assumption but requires importing topology here. -/
lemma sum_degree_eq_sum_order (G : IncidenceHypergraph ν ι ε) [Fintype V(G)] [Fintype E(G)] :
    ∑ v : V(G), G.degree v = ∑ e : E(G), G.order e :=
  G.sum_degree.trans G.sum_order.symm

variable {k l : ℕ∞}

/-! ### Uniformity and regularity -/

/-- Every active edge has order `k`, counting incidences with multiplicity.
For `k = ⊤`, this means that every active edge has infinitely many incidences. -/
def IsUniform (G : IncidenceHypergraph ν ι ε) (k : ℕ∞) : Prop :=
  ∀ e ∈ E(G), G.order e = k

/-- Every active vertex has degree `k`, counting incidences with multiplicity.
For `k = ⊤`, this means that every active vertex has infinitely many incidences. -/
def IsRegular (G : IncidenceHypergraph ν ι ε) (k : ℕ∞) : Prop :=
  ∀ v ∈ V(G), G.degree v = k

lemma IsUniform.order_eq (h : G.IsUniform k) (he : e ∈ E(G)) : G.order e = k :=
  h e he

lemma IsRegular.degree_eq (h : G.IsRegular k) (hv : v ∈ V(G)) : G.degree v = k :=
  h v hv

@[simp]
lemma isUniform_dual : G.dual.IsUniform k ↔ G.IsRegular k :=
  Iff.rfl

@[simp]
lemma isRegular_dual : G.dual.IsRegular k ↔ G.IsUniform k :=
  Iff.rfl

lemma IsUniform.eq_of_nonempty (hk : G.IsUniform k) (hl : G.IsUniform l) (hE : E(G).Nonempty) :
    k = l := by
  obtain ⟨e, he⟩ := hE
  exact (hk.order_eq he).symm.trans (hl.order_eq he)

lemma IsRegular.eq_of_nonempty (hk : G.IsRegular k) (hl : G.IsRegular l) (hV : V(G).Nonempty) :
    k = l :=
  IsUniform.eq_of_nonempty (G := G.dual) hk hl hV

lemma isUniform_of_edgeSet_eq_empty (hE : E(G) = ∅) : G.IsUniform k := by
  simp [IsUniform, hE]

lemma isRegular_of_vertexSet_eq_empty (hV : V(G) = ∅) : G.IsRegular k :=
  G.dual.isUniform_of_edgeSet_eq_empty hV

@[simp]
lemma isUniform_zero : G.IsUniform 0 ↔ I(G) = ∅ := by
  refine ⟨fun h ↦ eq_empty_iff_forall_notMem.mpr fun i hi ↦ ?_,
    fun h e he ↦ order_eq_zero_of_incidenceSet_eq_empty h⟩
  have hpos := G.order_edgeMap'_pos ⟨i, hi⟩
  rw [h.order_eq (G.edgeMap'_mem ⟨i, hi⟩)] at hpos
  exact lt_irrefl _ hpos

@[simp]
lemma isRegular_zero : G.IsRegular 0 ↔ I(G) = ∅ :=
  G.dual.isUniform_zero

end IncidenceHypergraph
