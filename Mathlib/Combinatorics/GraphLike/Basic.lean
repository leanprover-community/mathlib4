/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.PFun

/-!
# Presentations of graph-like objects

This module defines explicit presentations that capture common structure shared by graph objects
such as `SimpleGraph`, `Graph`, and `Digraph`.

Throughout this API, `G` denotes a graph-like object and `Gₚ` denotes a chosen presentation of
`G`.

## Main definitions

* `HypergraphPresentation`: presents a particular graph-like object using specified vertex,
  incidence, and edge types, together with incidence, source, target, link, and adjacency relations.
* `GraphLike`: requires every edge to have exactly two incidences, including a source incidence and
  a target incidence.
* `Undirected`: requires every incidence to be both a source and a target.
* `Directed`: requires source and target incidences to be disjoint.
* `NoParallelEdge`: requires two edges linking the same ordered pair of vertices to be equal.
* `Loopless`: requires distinct incidences of the same edge to have distinct endpoints.

## Implementation notes

`HypergraphPresentation` is a very general hypergraph structure that can be used to represent any
hypergraph/graph. However, it does not check that the presentation is coherent with the given graph;
for example, you can have K5 graph with hypergraph presentation that has no vertices. This is by
design, as it allows arbitrary objects to be presented as a hypergraph.
-/

public section

open Set Function

/-- A presentation of a particular graph-like object `G`, using separate types for vertices,
incidence identifiers, and edges.

The parameter `G` labels the object being presented. The fields specify the data of this
presentation; in particular, two presentations of the same `G` may use different incidence or edge
types. `Gₚ.IsIncident i e v` associates an incidence identifier `i` with an edge `e` and endpoint
`v`; each incidence identifier determines at most one such edge and endpoint. `IsSource` and
`IsTarget` orient the incidences. The derived relations `Gₚ.IsLink e u v` and `Gₚ.Adj u v` use two
distinct incidences of one edge, with a source at `u` and a target at `v`. -/
structure HypergraphPresentation (V I E : Type*) {Gr : Type*} (G : Gr) where
  /-- The set of vertices present in this presentation. -/
  verts : Set V
  /-- The set of edges present in this presentation. -/
  edges : Set E
  /-- `Gₚ.IsIncident i e v` means that `i` is an incidence of edge `e` at vertex `v`. -/
  IsIncident : I → E → V → Prop
  /-- The predicate that marks an incidence as a source incidence. -/
  IsSource : I → Prop
  /-- The predicate that marks an incidence as a target incidence. -/
  IsTarget : I → Prop
  /-- The endpoint of an incidence is present in the vertex set. -/
  vert_mem_of_isIncident ⦃i e v⦄ : IsIncident i e v → v ∈ verts
  /-- The edge of an incidence is present in the edge set. -/
  edge_mem_of_isIncident ⦃i e v⦄ : IsIncident i e v → e ∈ edges
  /-- An incidence identifier determines its edge and endpoint. -/
  eq_and_eq_of_isIncident_of_isIncident ⦃i e f u v⦄ :
    IsIncident i e u → IsIncident i f v → e = f ∧ u = v
  /-- An incidence identifier is used exactly when it is marked as a source or target. -/
  isIncident_iff ⦃i⦄ : (∃ e v, IsIncident i e v) ↔ IsSource i ∨ IsTarget i
  -- The following fields have defaults, and the accompanying fields state that an override agrees
  -- with its default.
  /-- The set of incidence identifiers used by this presentation. -/
  incs : Set I := {i | ∃ e v, IsIncident i e v}
  /-- `incs Gₚ` consists exactly of the identifiers participating in the incidence relation. -/
  incs_def : incs = {i | ∃ e v, IsIncident i e v} := by grind
  /-- `Gₚ.IsLink e u v` means that `e` has distinct source and target incidences at `u` and `v`. -/
  IsLink : E → V → V → Prop := fun e u v ↦ ∃ i j, i ≠ j ∧ IsSource i ∧ IsTarget j ∧
    IsIncident i e u ∧ IsIncident j e v
  /-- Characterizes `IsLink` in terms of the incidence, source, and target relations. -/
  isLink_def ⦃e u v⦄ : IsLink e u v ↔
    ∃ i j, i ≠ j ∧ IsSource i ∧ IsTarget j ∧ IsIncident i e u ∧ IsIncident j e v := by grind
  /-- `Gₚ.Adj u v` means that some edge links `u` to `v`. -/
  Adj : V → V → Prop := fun u v ↦ ∃ e i j, i ≠ j ∧ IsSource i ∧ IsTarget j ∧
    IsIncident i e u ∧ IsIncident j e v
  /-- Characterizes `Adj` in terms of the incidence, source, and target relations. -/
  adj_def ⦃u v⦄ : Adj u v ↔ ∃ e i j, i ≠ j ∧ IsSource i ∧ IsTarget j ∧
    IsIncident i e u ∧ IsIncident j e v := by grind

initialize_simps_projections HypergraphPresentation
  (as_prefix verts, as_prefix edges, as_prefix incs, IsIncident → isIncident,
    as_prefix isIncident, IsSource → isSource, as_prefix isSource, IsTarget → isTarget,
    as_prefix isTarget, IsLink → isLink, as_prefix isLink, Adj → adj, as_prefix adj)

namespace HypergraphPresentation

@[inherit_doc verts]
scoped notation "V(" Gₚ ")" => verts Gₚ

@[inherit_doc incs]
scoped notation "I(" Gₚ ")" => incs Gₚ

@[inherit_doc edges]
scoped notation "E(" Gₚ ")" => edges Gₚ

variable {V I E Gr : Type*} {G : Gr} {Gₚ : HypergraphPresentation V I E G} {u u' v v' w : V}
  {i j : I} {e f : E}

section HypergraphPresentation

lemma IsSource.mem (h : Gₚ.IsSource i) : i ∈ I(Gₚ) := by
  rw [Gₚ.incs_def, mem_ofPred_eq, Gₚ.isIncident_iff]
  exact Or.inl h

lemma IsTarget.mem (h : Gₚ.IsTarget i) : i ∈ I(Gₚ) := by
  rw [Gₚ.incs_def, mem_ofPred_eq, Gₚ.isIncident_iff]
  exact Or.inr h

@[ext] theorem incs_ext (i₁ i₂ : I(Gₚ)) (h : i₁.val = i₂.val) : i₁ = i₂ := Subtype.ext h

@[grind →]
lemma IsIncident.vert_mem (h : Gₚ.IsIncident i e v) : v ∈ V(Gₚ) :=
  Gₚ.vert_mem_of_isIncident h

@[grind →]
lemma IsIncident.edge_mem (h : Gₚ.IsIncident i e v) : e ∈ E(Gₚ) :=
  Gₚ.edge_mem_of_isIncident h

@[grind →]
lemma IsIncident.inc_mem (h : Gₚ.IsIncident i e v) : i ∈ I(Gₚ) :=
  Gₚ.incs_def ▸ ⟨e, v, h⟩

@[grind →]
lemma IsIncident.isSource_or_isTarget (h : Gₚ.IsIncident i e v) : Gₚ.IsSource i ∨ Gₚ.IsTarget i :=
  Gₚ.isIncident_iff.mp ⟨e, v, h⟩

lemma IsSource.exists_isIncident (h : Gₚ.IsSource i) : ∃ e v, Gₚ.IsIncident i e v :=
  Gₚ.isIncident_iff.mpr <| Or.inl h

lemma IsTarget.exists_isIncident (h : Gₚ.IsTarget i) : ∃ e v, Gₚ.IsIncident i e v :=
  Gₚ.isIncident_iff.mpr <| Or.inr h

@[grind →]
lemma IsIncident.inj (h : Gₚ.IsIncident i e u) (h' : Gₚ.IsIncident i f v) : e = f ∧ u = v :=
  Gₚ.eq_and_eq_of_isIncident_of_isIncident h h'

lemma unique_isIncident_of_mem_incs (h : i ∈ I(Gₚ)) : ∃! s : E × V, Gₚ.IsIncident i s.1 s.2 := by
  obtain ⟨e, v, hi⟩ := Gₚ.incs_def ▸ h
  use (e, v), hi, by grind

lemma Adj.left_mem (h : Gₚ.Adj v w) : v ∈ V(Gₚ) := by
  obtain ⟨e, i, j, hne, hi, hj, hei, hej⟩ := Gₚ.adj_def.mp h
  exact hei.vert_mem

lemma Adj.right_mem (h : Gₚ.Adj v w) : w ∈ V(Gₚ) := by
  obtain ⟨e, i, j, hne, hi, hj, hei, hej⟩ := Gₚ.adj_def.mp h
  exact hej.vert_mem

@[grind →]
lemma IsLink.edge_mem (h : Gₚ.IsLink e u v) : e ∈ E(Gₚ) := by
  obtain ⟨i, j, hne, hi, hj, hei, hej⟩ := Gₚ.isLink_def.mp h
  exact hei.edge_mem

@[grind →]
lemma IsLink.left_mem (h : Gₚ.IsLink e u v) : u ∈ V(Gₚ) := by
  obtain ⟨i, j, hne, hi, hj, hei, hej⟩ := Gₚ.isLink_def.mp h
  exact hei.vert_mem

@[grind →]
lemma IsLink.right_mem (h : Gₚ.IsLink e u v) : v ∈ V(Gₚ) := by
  obtain ⟨i, j, hne, hi, hj, hei, hej⟩ := Gₚ.isLink_def.mp h
  exact hej.vert_mem

@[grind →]
lemma IsLink.adj (h : Gₚ.IsLink e u v) : Gₚ.Adj u v :=
  Gₚ.adj_def.mpr ⟨e, Gₚ.isLink_def.mp h⟩

/-- The partial function that gives the edge of an incidence. Note that the output of this function
is `Part E`. If you need `E`, consider using `PFun.fn` or `PFun.asSubtype`. -/
noncomputable def edgeFun (Gₚ : HypergraphPresentation V I E G) : I →. E := fun i ↦
  letI := Classical.dec (i ∈ I(Gₚ))
  if h : i ∈ I(Gₚ) then Part.some (Gₚ.incs_def ▸ h).choose else Part.none

@[simp, grind =]
lemma dom_edgeFun (Gₚ : HypergraphPresentation V I E G) : Gₚ.edgeFun.Dom = I(Gₚ) := by
  ext i
  simp +contextual only [PFun.mem_dom, edgeFun, iff_def, forall_exists_index, ↓reduceDIte,
    Part.mem_some_iff, exists_eq, implies_true, and_true]
  split_ifs with hi
  · simpa
  simp

lemma mem_incs_of_mem_edgeFun (hei : e ∈ Gₚ.edgeFun i) : i ∈ I(Gₚ) := by
  rw [← dom_edgeFun]
  exact Part.dom_iff_mem.mpr ⟨e, hei⟩

/-- The partial function that gives the end point of an incidence. Note that the output of this
function is `Part V`. If you need `V`, consider using `PFun.fn` or `PFun.asSubtype`. -/
noncomputable def endPoint (Gₚ : HypergraphPresentation V I E G) : I →. V := fun i ↦
  letI := Classical.dec (i ∈ I(Gₚ))
  if h : i ∈ I(Gₚ) then Part.some (Gₚ.incs_def ▸ h).choose_spec.choose else Part.none

@[simp, grind =]
lemma dom_endPoint (Gₚ : HypergraphPresentation V I E G) : Gₚ.endPoint.Dom = I(Gₚ) := by
  ext i
  simp +contextual only [PFun.mem_dom, endPoint, iff_def, forall_exists_index, ↓reduceDIte,
    Part.mem_some_iff, exists_eq, implies_true, and_true]
  split_ifs with hi
  · simpa
  simp

lemma mem_incs_of_mem_endPoint (hvi : v ∈ Gₚ.endPoint i) : i ∈ I(Gₚ) := by
  rw [← dom_endPoint]
  exact Part.dom_iff_mem.mpr ⟨v, hvi⟩

lemma isIncident_edgeFun_endPoint (hi : i ∈ I(Gₚ)) : Gₚ.IsIncident i
    (Gₚ.edgeFun.fn i (dom_edgeFun Gₚ ▸ hi)) (Gₚ.endPoint.fn i (dom_endPoint Gₚ ▸ hi)) := by
  simp only [PFun.fn_apply, edgeFun, hi, ↓reduceDIte, Part.get_some, endPoint]
  exact (Gₚ.incs_def ▸ hi).choose_spec.choose_spec

@[grind →]
lemma IsIncident.mem_edgeFun (h : Gₚ.IsIncident i e v) : e ∈ Gₚ.edgeFun i := by
  rw [← ((isIncident_edgeFun_endPoint h.inc_mem).inj h).1]
  exact Part.get_mem _

@[grind →]
lemma IsIncident.mem_endPoint (h : Gₚ.IsIncident i e v) : v ∈ Gₚ.endPoint i := by
  rw [← ((isIncident_edgeFun_endPoint h.inc_mem).inj h).2]
  exact Part.get_mem _

@[simp, grind =]
lemma mem_edgeFun_iff_exists_isIncident (Gₚ : HypergraphPresentation V I E G) (e : E) (i : I) :
    e ∈ Gₚ.edgeFun i ↔ ∃ v, Gₚ.IsIncident i e v := by
  refine ⟨fun hei ↦ ?_, fun ⟨v, hei⟩ ↦ hei.mem_edgeFun⟩
  have hi := mem_incs_of_mem_edgeFun hei
  exact ⟨Gₚ.endPoint.fn i (dom_endPoint Gₚ ▸ hi),
    (Part.mem_unique (Part.get_mem _) hei) ▸ Gₚ.isIncident_edgeFun_endPoint hi⟩

@[simp, grind =]
lemma mem_endPoint_iff_exists_isIncident (Gₚ : HypergraphPresentation V I E G) (i : I) (v : V) :
    v ∈ Gₚ.endPoint i ↔ ∃ e, Gₚ.IsIncident i e v := by
  refine ⟨fun hvi ↦ ?_, fun ⟨e, hei⟩ ↦ hei.mem_endPoint⟩
  have hi := mem_incs_of_mem_endPoint hvi
  exact ⟨Gₚ.edgeFun.fn i (Gₚ.dom_edgeFun ▸ hi),
    (Part.mem_unique (Part.get_mem _) hvi) ▸ Gₚ.isIncident_edgeFun_endPoint hi⟩

@[grind =]
lemma mem_edgeFun_mem_endPoint_iff_isIncident (Gₚ : HypergraphPresentation V I E G) (i : I) (e : E)
    (v : V) : e ∈ Gₚ.edgeFun i ∧ v ∈ Gₚ.endPoint i ↔ Gₚ.IsIncident i e v := by
  refine ⟨fun ⟨hei, hvi⟩ ↦ ?_, fun h ↦ ⟨h.mem_edgeFun, h.mem_endPoint⟩⟩
  have hi := mem_incs_of_mem_edgeFun hei
  have he : Gₚ.edgeFun.fn i (dom_edgeFun Gₚ ▸ hi) = e := Part.mem_unique (Part.get_mem _) hei
  exact he ▸ (Part.mem_unique (Part.get_mem _) hvi) ▸ isIncident_edgeFun_endPoint hi

/-- The order of an edge is the number of incidences of the edge. -/
@[expose]
noncomputable def order (Gₚ : HypergraphPresentation V I E G) (e : E) : ℕ∞ :=
  (Gₚ.edgeFun |>.preimage {e}).encard

/-- The degree of a vertex is the number of incidences of the vertex. -/
@[expose]
noncomputable def degree (Gₚ : HypergraphPresentation V I E G) (v : V) : ℕ∞ :=
  (Gₚ.endPoint |>.preimage {v}).encard

lemma edgeFun_preimage_singleton_injOn (h : ∀ e ∈ E(Gₚ), order Gₚ e ≠ 0) :
    InjOn (Gₚ.edgeFun |>.preimage {·}) E(Gₚ) := by
  rintro e he f hf heq
  contrapose! heq
  simp only [order, ne_eq, encard_eq_zero, ← nonempty_iff_ne_empty] at h
  obtain ⟨i, hi⟩ := h e he
  have hef : Disjoint (Gₚ.edgeFun |>.preimage {e}) (Gₚ.edgeFun |>.preimage {f}) :=
    PFun.disjoint_preimage_of_disjoint _ <| by simpa
  exact hef.ne (by simp [← nonempty_iff_ne_empty, h e he])

end HypergraphPresentation

section GraphLike

/-- A `HypergraphPresentation` is `GraphLike` if every edge in the presentation has exactly two
incidences, including a source incidence and a target incidence. -/
class GraphLike (Gₚ : HypergraphPresentation V I E G) : Prop where
  /-- Every edge present in the structure has exactly two incidences. -/
  order_eq_two ⦃e : E⦄ : e ∈ E(Gₚ) → order Gₚ e = 2
  /-- Every edge present in the structure has a source incidence. -/
  exists_isSource_of_mem_edgeSet ⦃e : E⦄ :
    e ∈ E(Gₚ) → ∃ i, e ∈ Gₚ.edgeFun i ∧ Gₚ.IsSource i
  /-- Every edge present in the structure has a target incidence. -/
  exists_isTarget_of_mem_edgeSet ⦃e : E⦄ :
    e ∈ E(Gₚ) → ∃ i, e ∈ Gₚ.edgeFun i ∧ Gₚ.IsTarget i

variable [GraphLike Gₚ]

lemma order_eq_two (he : e ∈ E(Gₚ)) : order Gₚ e = 2 := GraphLike.order_eq_two he

lemma exists_isSource_of_mem_edgeSet (he : e ∈ E(Gₚ)) : ∃ i, e ∈ Gₚ.edgeFun i ∧ Gₚ.IsSource i :=
  GraphLike.exists_isSource_of_mem_edgeSet he

lemma exists_isTarget_of_mem_edgeSet (he : e ∈ E(Gₚ)) : ∃ i, e ∈ Gₚ.edgeFun i ∧ Gₚ.IsTarget i :=
  GraphLike.exists_isTarget_of_mem_edgeSet he

lemma exists_pair_mem_edgeFun_iff (he : e ∈ E(Gₚ)) :
    ∃ i j, i ≠ j ∧ ∀ (x : I), e ∈ Gₚ.edgeFun x ↔ x = i ∨ x = j := by
  simpa [order, encard_eq_two, Set.ext_iff] using order_eq_two he

lemma exists_isLink_of_mem_edgeSet (he : e ∈ E(Gₚ)) : ∃ u v, Gₚ.IsLink e u v := by
  simp_rw [Gₚ.isLink_def]
  obtain ⟨i, j, hne, hei⟩ := exists_pair_mem_edgeFun_iff he
  grind [hei i, hei j, exists_isSource_of_mem_edgeSet he, exists_isTarget_of_mem_edgeSet he]

@[grind <=]
lemma IsLink.eq_or_eq_of_isLink (h : Gₚ.IsLink e u v) (h' : Gₚ.IsLink e u' v') :
    u = u' ∧ v = v' ∨ u = v' ∧ v = u' := by
  obtain ⟨i, j, hij, hi, hj, hi', hj'⟩ := Gₚ.isLink_def.mp h
  obtain ⟨i', j', hij', hi', hj', hi'', hj''⟩ := Gₚ.isLink_def.mp h'
  obtain ⟨k, l, hkl, h⟩ := exists_pair_mem_edgeFun_iff hi''.edge_mem
  grind

lemma edgeFun_preimage_singleton_injOn_of_GraphLike : InjOn ((Gₚ.edgeFun) |>.preimage {·}) E(Gₚ) :=
  edgeFun_preimage_singleton_injOn fun e he ↦ by simp [order_eq_two he]

end GraphLike

section Undirected

/-- A presentation is undirected if every source incidence is a target incidence and vice versa. -/
class Undirected (Gₚ : HypergraphPresentation V I E G) : Prop where
  /-- Source and target incidences coincide. -/
  isSource_iff ⦃i : I⦄ : Gₚ.IsSource i ↔ Gₚ.IsTarget i

variable [Undirected Gₚ]

@[simp, grind =]
lemma isSource_iff (Gₚ : HypergraphPresentation V I E G) [Undirected Gₚ] (i : I) :
    Gₚ.IsSource i ↔ Gₚ.IsTarget i :=
  Undirected.isSource_iff (Gₚ := Gₚ) (i := i)

lemma IsIncident.isSource (h : Gₚ.IsIncident i e v) : Gₚ.IsSource i := by grind
lemma IsIncident.isTarget (h : Gₚ.IsIncident i e v) : Gₚ.IsTarget i := by grind

@[grind →]
lemma isSource_of_mem_incs (hi : i ∈ I(Gₚ)) : Gₚ.IsSource i := by
  obtain ⟨e, v, hi⟩ := Gₚ.incs_def ▸ hi
  exact hi.isSource

@[grind →]
lemma isTarget_of_mem_incs (hi : i ∈ I(Gₚ)) : Gₚ.IsTarget i := by
  obtain ⟨e, v, hi⟩ := Gₚ.incs_def ▸ hi
  exact hi.isTarget

lemma isLink_iff_of_undirected : Gₚ.IsLink e u v ↔
    ∃ i j, i ≠ j ∧ Gₚ.IsIncident i e u ∧ Gₚ.IsIncident j e v :=
  Gₚ.isLink_def.trans ⟨fun ⟨i, j, hne, _, _, hi, hj⟩ ↦ ⟨i, j, hne, hi, hj⟩,
    fun ⟨i, j, hne, hi, hj⟩ ↦ ⟨i, j, hne, hi.isSource, hj.isTarget, hi, hj⟩⟩

instance : Std.Symm (Gₚ.Adj) where
  symm _ _ h := by grind [Gₚ.adj_def]

@[symm] lemma Adj.symm (h : Gₚ.Adj v w) : Gₚ.Adj w v := symm_of (Gₚ.Adj) h

lemma adj_comm : Gₚ.Adj v w ↔ Gₚ.Adj w v := ⟨symm_of (Gₚ.Adj), symm_of (Gₚ.Adj)⟩

end Undirected

section Directed

/-- A presentation is directed if no incidence is both a source and a target. -/
class Directed (Gₚ : HypergraphPresentation V I E G) : Prop where
  /-- A source incidence is not a target incidence. -/
  not_isTarget_of_isSource ⦃i : I⦄ : Gₚ.IsSource i → ¬ Gₚ.IsTarget i

variable [Directed Gₚ]

@[grind →]
lemma IsSource.not_isTarget (h : Gₚ.IsSource i) : ¬ Gₚ.IsTarget i :=
  Directed.not_isTarget_of_isSource h

lemma IsTarget.not_isSource (h : Gₚ.IsTarget i) : ¬ Gₚ.IsSource i := by grind

end Directed

section NoParallelEdge

/-
### GraphLike with no parallel edges

Some graph-like presentations, such as those for `SimpleGraph` and `Digraph`, do not allow
distinct edges between the same ordered pair of vertices.
-/

/-- A presentation has no parallel edges if two edges linking the same ordered pair of vertices are
equal. This includes the standard presentations of `SimpleGraph` and `Digraph`. -/
class NoParallelEdge (Gₚ : HypergraphPresentation V I E G) [GraphLike Gₚ] : Prop where
  /-- Two edges linking the same ordered pair of vertices are equal. -/
  edge_eq_of_isLink {e f : E} {u v : V} : Gₚ.IsLink e u v → Gₚ.IsLink f u v → e = f

variable [GraphLike Gₚ] [NoParallelEdge Gₚ]

lemma IsLink.edge_eq (h : Gₚ.IsLink e u v) (h' : Gₚ.IsLink f u v) : e = f :=
  NoParallelEdge.edge_eq_of_isLink h h'

end NoParallelEdge

section Loopless

/-- A presentation is loopless if distinct incidences of the same edge have distinct endpoints. -/
class Loopless (Gₚ : HypergraphPresentation V I E G) : Prop where
  /-- Distinct incidences of the same edge have distinct endpoints. -/
  no_loops_of_mem_mem ⦃i j : I⦄ : i ∈ I(Gₚ) → j ∈ I(Gₚ) → Gₚ.edgeFun i = Gₚ.edgeFun j → i ≠ j →
    Gₚ.endPoint i ≠ Gₚ.endPoint j

variable [Loopless Gₚ]

lemma no_loops_of_left_mem (hi : i ∈ I(Gₚ)) (hij : Gₚ.edgeFun i = Gₚ.edgeFun j) (hne : i ≠ j) :
    Gₚ.endPoint i ≠ Gₚ.endPoint j := by
  obtain ⟨e, he⟩ := Part.dom_iff_mem.mp (dom_edgeFun Gₚ ▸ hi)
  exact Loopless.no_loops_of_mem_mem hi (mem_incs_of_mem_edgeFun (hij ▸ he)) hij hne

lemma no_loops_of_right_mem (hj : j ∈ I(Gₚ)) (hij : Gₚ.edgeFun i = Gₚ.edgeFun j) (hne : i ≠ j) :
    Gₚ.endPoint i ≠ Gₚ.endPoint j := by
  obtain ⟨e, he⟩ := Part.dom_iff_mem.mp (dom_edgeFun Gₚ ▸ hj)
  exact Loopless.no_loops_of_mem_mem (mem_incs_of_mem_edgeFun (hij ▸ he)) hj hij hne

lemma IsIncident.inc_inj (hi : Gₚ.IsIncident i e v) (hj : Gₚ.IsIncident j e v) : i = j := by
  obtain ⟨hei, hvi⟩ := (mem_edgeFun_mem_endPoint_iff_isIncident ..).mpr hi
  obtain ⟨hej, hvj⟩ := (mem_edgeFun_mem_endPoint_iff_isIncident ..).mpr hj
  exact not_imp_not.mp (no_loops_of_left_mem hi.inc_mem (Part.mem_right_unique hei hej))
    (Part.mem_right_unique hvi hvj)

end Loopless

end HypergraphPresentation
