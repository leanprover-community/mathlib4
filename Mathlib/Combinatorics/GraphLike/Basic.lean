/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Thomas Waring
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Set.Card
public import Mathlib.Data.PFun
public import Mathlib.Order.Partition.Basic

/-!
# Typeclasses for graph-like structures

This module defines typeclasses that capture common structure shared by graph representations such
as `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `HyperGraphLike`: records the vertices, edges, and incidence identifiers of a graph-like
  structure, together with the incidence, source, target, link, and adjacency relations.
* `GraphLike`: requires every edge to have exactly two incidences, including a source incidence and
  a target incidence.
* `Undirected`: requires every incidence to be both a source and a target.
* `Directed`: requires source and target incidences to be disjoint.
* `NoParallelEdge`: requires two edges linking the same ordered pair of vertices to be equal.
* `Loopless`: requires distinct incidences of the same edge to have distinct endpoints.

-/

public section

open Set Function

/-- `HyperGraphLike` abstracts a graph-like structure using separate types for vertices, incidence
identifiers, and edges.

Consider a type that models a graph-like structure, `Gr`. For `G : Gr`, `verts G` and `edges G`
specify the vertices and edges present in `G`. `IsIncident G i e v` associates an incidence
identifier `i` with an edge `e` and endpoint `v`; each incidence identifier determines at most one
such edge and endpoint. `IsSource` and `IsTarget` orient the incidences. The derived relations
`IsLink G e u v` and `Adj G u v` use two distinct incidences of one edge, with a source at `u` and a
target at `v`. -/
class HyperGraphLike (V I E : outParam Type*) (Gr : Type*) where
  /-- The set of vertices present in a graph-like structure. -/
  verts : Gr → Set V
  /-- The set of edges present in a graph-like structure. -/
  edges : Gr → Set E
  /-- `IsIncident G i e v` means that `i` is an incidence of edge `e` at vertex `v` in `G`. -/
  IsIncident : Gr → I → E → V → Prop
  /-- The predicate that marks an incidence as a source incidence. -/
  IsSource : Gr → I → Prop
  /-- The predicate that marks an incidence as a target incidence. -/
  IsTarget : Gr → I → Prop
  /-- The endpoint of an incidence is present in the vertex set. -/
  vert_mem_of_isIncident ⦃G i e v⦄ : IsIncident G i e v → v ∈ verts G
  /-- The edge of an incidence is present in the edge set. -/
  edge_mem_of_isIncident ⦃G i e v⦄ : IsIncident G i e v → e ∈ edges G
  /-- An incidence identifier determines its edge and endpoint. -/
  eq_and_eq_of_isIncident_of_isIncident ⦃G i e f u v⦄ :
    IsIncident G i e u → IsIncident G i f v → e = f ∧ u = v
  /-- An incidence identifier is used exactly when it is marked as a source or target. -/
  isIncident_iff ⦃G i⦄ : (∃ e v, IsIncident G i e v) ↔ IsSource G i ∨ IsTarget G i
  -- The following fields have defaults, and the accompanying fields state that an override agrees
  -- with its default.
  /-- The set of incidence identifiers used by a graph-like structure. -/
  incs : Gr → Set I := fun G ↦ {i | ∃ e v, IsIncident G i e v}
  /-- `incs G` consists exactly of the identifiers participating in the incidence relation. -/
  incs_def ⦃G⦄ : incs G = {i | ∃ e v, IsIncident G i e v} := by grind
  /-- `IsLink G e u v` means that `e` has distinct source and target incidences at `u` and `v`. -/
  IsLink : Gr → E → V → V → Prop := fun G e u v ↦ ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧
    IsIncident G i e u ∧ IsIncident G j e v
  /-- Characterizes `IsLink` in terms of the incidence, source, and target relations. -/
  isLink_def ⦃G e u v⦄ : IsLink G e u v ↔
    ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ IsIncident G i e u ∧ IsIncident G j e v := by grind
  /-- `Adj G u v` means that some edge links `u` to `v`. -/
  Adj : Gr → V → V → Prop := fun G u v ↦ ∃ e i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧
    IsIncident G i e u ∧ IsIncident G j e v
  /-- Characterizes `Adj` in terms of the incidence, source, and target relations. -/
  adj_def ⦃G u v⦄ : Adj G u v ↔ ∃ e i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧
    IsIncident G i e u ∧ IsIncident G j e v := by grind

initialize_simps_projections HyperGraphLike (as_prefix verts, as_prefix edges, as_prefix incs,
  IsIncident → isIncident, as_prefix isIncident, IsSource → isSource, as_prefix isSource,
  IsTarget → isTarget, as_prefix isTarget, IsLink → isLink, as_prefix isLink, Adj → adj,
  as_prefix adj)

namespace HyperGraphLike

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

@[inherit_doc incs]
scoped notation "I(" G ")" => incs G

@[inherit_doc edges]
scoped notation "E(" G ")" => edges G

variable {V I E Gr : Type*} {G : Gr} [HyperGraphLike V I E Gr] {u u' v v' w : V} {i j : I}
  {e f : E}

section HyperGraphLike

lemma IsSource.mem (h : IsSource G i) : i ∈ I(G) := by
  rw [incs_def, mem_ofPred_eq, isIncident_iff]
  exact Or.inl h

lemma IsTarget.mem (h : IsTarget G i) : i ∈ I(G) := by
  rw [incs_def, mem_ofPred_eq, isIncident_iff]
  exact Or.inr h

@[ext] theorem incs_ext (i₁ i₂ : I(G)) (h : i₁.val = i₂.val) : i₁ = i₂ := Subtype.ext h

@[grind →]
lemma IsIncident.vert_mem (h : IsIncident G i e v) : v ∈ V(G) :=
  vert_mem_of_isIncident h

@[grind →]
lemma IsIncident.edge_mem (h : IsIncident G i e v) : e ∈ E(G) :=
  edge_mem_of_isIncident h

@[grind →]
lemma IsIncident.inc_mem (h : IsIncident G i e v) : i ∈ I(G) :=
  incs_def (G := G) ▸ ⟨e, v, h⟩

@[grind →]
lemma IsIncident.isSource_or_isTarget (h : IsIncident G i e v) : IsSource G i ∨ IsTarget G i :=
  isIncident_iff.mp ⟨e, v, h⟩

lemma IsSource.exists_isIncident (h : IsSource G i) : ∃ e v, IsIncident G i e v :=
  isIncident_iff.mpr <| Or.inl h

lemma IsTarget.exists_isIncident (h : IsTarget G i) : ∃ e v, IsIncident G i e v :=
  isIncident_iff.mpr <| Or.inr h

@[grind →]
lemma IsIncident.inj (h : IsIncident G i e u) (h' : IsIncident G i f v) : e = f ∧ u = v :=
  eq_and_eq_of_isIncident_of_isIncident h h'

lemma unique_isIncident_of_mem_incs (h : i ∈ I(G)) : ∃! s : E × V, IsIncident G i s.1 s.2 := by
  obtain ⟨e, v, hi⟩ := incs_def (G := G) ▸ h
  use (e, v), hi, by grind

lemma IsIncident.unique_or_bot (G : Gr) (i : I) :
    (∃! s : E × V, IsIncident G i s.1 s.2) ∨ IsIncident G i = ⊥ := by
  by_cases hi : i ∈ I(G)
  · exact Or.inl (unique_isIncident_of_mem_incs hi)
  right
  ext e v
  simp only [incs_def, mem_ofPred_eq, not_exists, Pi.bot_apply, «Prop».bot_eq_false,
    iff_false] at hi ⊢
  exact hi e v

lemma Adj.left_mem (h : Adj G v w) : v ∈ V(G) := by
  obtain ⟨e, i, j, hne, hi, hj, hei, hej⟩ := adj_def.mp h
  exact hei.vert_mem

lemma Adj.right_mem (h : Adj G v w) : w ∈ V(G) := by
  obtain ⟨e, i, j, hne, hi, hj, hei, hej⟩ := adj_def.mp h
  exact hej.vert_mem

@[grind →]
lemma IsLink.edge_mem (h : IsLink G e u v) : e ∈ E(G) := by
  obtain ⟨i, j, hne, hi, hj, hei, hej⟩ := isLink_def.mp h
  exact hei.edge_mem

@[grind →]
lemma IsLink.left_mem (h : IsLink G e u v) : u ∈ V(G) := by
  obtain ⟨i, j, hne, hi, hj, hei, hej⟩ := isLink_def.mp h
  exact hei.vert_mem

@[grind →]
lemma IsLink.right_mem (h : IsLink G e u v) : v ∈ V(G) := by
  obtain ⟨i, j, hne, hi, hj, hei, hej⟩ := isLink_def.mp h
  exact hej.vert_mem

@[grind →]
lemma IsLink.adj (h : IsLink G e u v) : Adj G u v := adj_def.mpr ⟨e, isLink_def.mp h⟩

/-- The partial function that gives the edge of an incidence. Note that the output of this function
is `Part E`. If you need `E`, consider using `PFun.fn` or `PFun.asSubtype`. -/
noncomputable def edgeFun (G : Gr) : I →. E := fun i ↦
  letI := Classical.dec (i ∈ I(G))
  if h : i ∈ I(G) then Part.some (incs_def (G := G) ▸ h).choose else Part.none

@[simp, grind =]
lemma dom_edgeFun (G : Gr) : (edgeFun G).Dom = I(G) := by
  ext i
  simp +contextual only [PFun.mem_dom, edgeFun, iff_def, forall_exists_index, ↓reduceDIte,
    Part.mem_some_iff, exists_eq, implies_true, and_true]
  split_ifs with hi
  · simpa
  simp

lemma mem_incs_of_mem_edgeFun (hei : e ∈ edgeFun G i) : i ∈ I(G) := by
  rw [← dom_edgeFun]
  exact Part.dom_iff_mem.mpr ⟨e, hei⟩

/-- The partial function that gives the end point of an incidence. Note that the output of this
function is `Part V`. If you need `V`, consider using `PFun.fn` or `PFun.asSubtype`. -/
noncomputable def endPoint (G : Gr) : I →. V := fun i ↦
  letI := Classical.dec (i ∈ I(G))
  if h : i ∈ I(G) then Part.some (incs_def (G := G) ▸ h).choose_spec.choose else Part.none

@[simp, grind =]
lemma dom_endPoint (G : Gr) : (endPoint G).Dom = I(G) := by
  ext i
  simp +contextual only [PFun.mem_dom, endPoint, iff_def, forall_exists_index, ↓reduceDIte,
    Part.mem_some_iff, exists_eq, implies_true, and_true]
  split_ifs with hi
  · simpa
  simp

lemma mem_incs_of_mem_endPoint (hvi : v ∈ endPoint G i) : i ∈ I(G) := by
  rw [← dom_endPoint]
  exact Part.dom_iff_mem.mpr ⟨v, hvi⟩

lemma isIncident_edgeFun_endPoint (hi : i ∈ I(G)) : IsIncident G i
    ((edgeFun G).fn i (dom_edgeFun G ▸ hi)) ((endPoint G).fn i (dom_endPoint G ▸ hi)) := by
  simp only [PFun.fn_apply, edgeFun, hi, ↓reduceDIte, Part.get_some, endPoint]
  exact (incs_def (G := G) ▸ hi).choose_spec.choose_spec

@[grind →]
lemma IsIncident.mem_edgeFun (h : IsIncident G i e v) : e ∈ edgeFun G i := by
  rw [← ((isIncident_edgeFun_endPoint h.inc_mem).inj h).1]
  exact Part.get_mem _

@[grind →]
lemma IsIncident.mem_endPoint (h : IsIncident G i e v) : v ∈ endPoint G i := by
  rw [← ((isIncident_edgeFun_endPoint h.inc_mem).inj h).2]
  exact Part.get_mem _

@[simp, grind =]
lemma mem_edgeFun_iff_exists_isIncident (G : Gr) (e : E) (i : I) :
    e ∈ edgeFun G i ↔ ∃ v, IsIncident G i e v := by
  refine ⟨fun hei ↦ ?_, fun ⟨v, hei⟩ ↦ hei.mem_edgeFun⟩
  have hi := mem_incs_of_mem_edgeFun hei
  exact ⟨(endPoint G).fn i (dom_endPoint G ▸ hi),
    (Part.mem_unique (Part.get_mem _) hei) ▸ isIncident_edgeFun_endPoint hi⟩

@[simp, grind =]
lemma mem_endPoint_iff_exists_isIncident (G : Gr) (i : I) (v : V) :
    v ∈ endPoint G i ↔ ∃ e, IsIncident G i e v := by
  refine ⟨fun hvi ↦ ?_, fun ⟨e, hei⟩ ↦ hei.mem_endPoint⟩
  have hi := mem_incs_of_mem_endPoint hvi
  exact ⟨(edgeFun G).fn i (dom_edgeFun G ▸ hi),
    (Part.mem_unique (Part.get_mem _) hvi) ▸ isIncident_edgeFun_endPoint hi⟩

@[grind =]
lemma mem_edgeFun_mem_endPoint_iff_isIncident (G : Gr) (i : I) (e : E) (v : V) :
    e ∈ edgeFun G i ∧ v ∈ endPoint G i ↔ IsIncident G i e v := by
  refine ⟨fun ⟨hei, hvi⟩ ↦ ?_, fun h ↦ ⟨h.mem_edgeFun, h.mem_endPoint⟩⟩
  have hi := mem_incs_of_mem_edgeFun hei
  have he : (edgeFun G).fn i (dom_edgeFun G ▸ hi) = e :=
    Part.mem_unique (Part.get_mem _) hei
  exact he ▸ (Part.mem_unique (Part.get_mem _) hvi) ▸ isIncident_edgeFun_endPoint hi

/-- The order of an edge is the number of incidences of the edge. -/
@[expose]
noncomputable def order (G : Gr) (e : E) : ℕ∞ := (edgeFun G |>.preimage {e}).encard

/-- The degree of a vertex is the number of incidences of the vertex. -/
@[expose]
noncomputable def degree (G : Gr) (v : V) : ℕ∞ := (endPoint G |>.preimage {v}).encard

lemma edgeFun_preimage_singleton_injOn (h : ∀ e ∈ E(G), order G e ≠ 0) :
    InjOn (edgeFun G |>.preimage {·}) E(G) := by
  rintro e he f hf heq
  contrapose! heq
  simp only [order, ne_eq, encard_eq_zero, ← nonempty_iff_ne_empty] at h
  obtain ⟨i, hi⟩ := h e he
  have hef : Disjoint (edgeFun G |>.preimage {e}) (edgeFun G |>.preimage {f}) :=
    PFun.disjoint_preimage_of_disjoint _ <| by simpa
  exact hef.ne (by simp [← nonempty_iff_ne_empty, h e he])

end HyperGraphLike

section GraphLike

/-- A `HyperGraphLike` structure is `GraphLike` if every edge present in the structure has exactly
two incidences, including a source incidence and a target incidence. -/
class GraphLike (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
  /-- Every edge present in the structure has exactly two incidences. -/
  order_eq_two ⦃G : Gr⦄ ⦃e : E⦄ : e ∈ E(G) → order G e = 2
  /-- Every edge present in the structure has a source incidence. -/
  exists_isSource_of_mem_edgeSet ⦃G : Gr⦄ ⦃e : E⦄ : e ∈ E(G) → ∃ i, e ∈ edgeFun G i ∧ IsSource G i
  /-- Every edge present in the structure has a target incidence. -/
  exists_isTarget_of_mem_edgeSet ⦃G : Gr⦄ ⦃e : E⦄ : e ∈ E(G) → ∃ i, e ∈ edgeFun G i ∧ IsTarget G i

variable [GraphLike V I E Gr]

lemma order_eq_two (he : e ∈ E(G)) : order G e = 2 := GraphLike.order_eq_two he

lemma exists_isSource_of_mem_edgeSet (he : e ∈ E(G)) : ∃ i, e ∈ edgeFun G i ∧ IsSource G i :=
  GraphLike.exists_isSource_of_mem_edgeSet he

lemma exists_isTarget_of_mem_edgeSet (he : e ∈ E(G)) : ∃ i, e ∈ edgeFun G i ∧ IsTarget G i :=
  GraphLike.exists_isTarget_of_mem_edgeSet he

lemma exists_pair_mem_edgeFun_iff (he : e ∈ E(G)) :
    ∃ i j, i ≠ j ∧ ∀ (x : I), e ∈ edgeFun G x ↔ x = i ∨ x = j := by
  simpa [order, encard_eq_two, Set.ext_iff] using order_eq_two he

lemma exists_isLink_of_mem_edgeSet (he : e ∈ E(G)) : ∃ u v, IsLink G e u v := by
  simp_rw [isLink_def]
  obtain ⟨i, j, hne, hei⟩ := exists_pair_mem_edgeFun_iff he
  have hS := exists_isSource_of_mem_edgeSet he
  have hT := exists_isTarget_of_mem_edgeSet he
  grind [hei i, hei j]

@[grind <=]
lemma IsLink.eq_or_eq_of_isLink (h : IsLink G e u v) (h' : IsLink G e u' v') :
    u = u' ∧ v = v' ∨ u = v' ∧ v = u' := by
  obtain ⟨i, j, hij, hi, hj, hi', hj'⟩ := isLink_def.mp h
  obtain ⟨i', j', hij', hi', hj', hi'', hj''⟩ := isLink_def.mp h'
  obtain ⟨k, l, hkl, h⟩ := exists_pair_mem_edgeFun_iff hi''.edge_mem
  grind

lemma edgeFun_preimage_singleton_injOn_of_GraphLike : InjOn ((edgeFun G) |>.preimage {·}) E(G) :=
  edgeFun_preimage_singleton_injOn (G := G) fun e he ↦ by simp [order_eq_two he]

end GraphLike

section Undirected

/-- A graph-like structure is undirected if every source incidence is a target incidence and
vice versa. -/
class Undirected (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
  /-- Source and target incidences coincide. -/
  isSource_iff ⦃G : Gr⦄ ⦃i : I⦄ : IsSource G i ↔ IsTarget G i

variable [Undirected V I E Gr]

@[simp, grind =]
lemma isSource_iff (G : Gr) (i : I) : IsSource G i ↔ IsTarget G i :=
  Undirected.isSource_iff (G := G) (i := i)

lemma IsIncident.isSource (h : IsIncident G i e v) : IsSource G i := by grind
lemma IsIncident.isTarget (h : IsIncident G i e v) : IsTarget G i := by grind

@[grind →]
lemma isSource_of_mem_incs (hi : i ∈ I(G)) : IsSource G i := by
  rw [incs_def] at hi
  obtain ⟨e, v, hi⟩ := hi
  exact hi.isSource

@[grind →]
lemma isTarget_of_mem_incs (hi : i ∈ I(G)) : IsTarget G i := by
  rw [incs_def] at hi
  obtain ⟨e, v, hi⟩ := hi
  exact hi.isTarget

lemma isLink_iff_of_undirected : IsLink G e u v ↔
    ∃ i j, i ≠ j ∧ IsIncident G i e u ∧ IsIncident G j e v :=
  isLink_def.trans ⟨fun ⟨i, j, hne, _, _, hi, hj⟩ ↦ ⟨i, j, hne, hi, hj⟩,
    fun ⟨i, j, hne, hi, hj⟩ ↦ ⟨i, j, hne, hi.isSource, hj.isTarget, hi, hj⟩⟩

instance : Std.Symm (Adj G) where
  symm _ _ h := by grind [adj_def]

@[symm] lemma Adj.symm (h : Adj G v w) : Adj G w v := symm_of (Adj G) h

lemma adj_comm : Adj G v w ↔ Adj G w v := ⟨symm_of (Adj G), symm_of (Adj G)⟩

end Undirected

section Directed

/-- A graph-like structure is directed if no incidence is both a source and a target. -/
class Directed (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
  /-- A source incidence is not a target incidence. -/
  not_isTarget_of_isSource ⦃G : Gr⦄ ⦃i : I⦄ : IsSource G i → ¬ IsTarget G i
  /-- A target incidence is not a source incidence. -/
  not_isSource_of_isTarget ⦃G : Gr⦄ ⦃i : I⦄ : IsTarget G i → ¬ IsSource G i

variable [Directed V I E Gr]

@[grind →]
lemma IsSource.not_isTarget (h : IsSource G i) : ¬ IsTarget G i :=
  Directed.not_isTarget_of_isSource h

@[grind →]
lemma IsTarget.not_isSource (h : IsTarget G i) : ¬ IsSource G i :=
  Directed.not_isSource_of_isTarget h

end Directed

section NoParallelEdge

/-
### GraphLike with no parallel edges

Some graph-like structures, such as `SimpleGraph` and `Digraph`, do not allow distinct edges
between the same ordered pair of vertices.
-/

/-- A graph-like structure has no parallel edges if two edges linking the same ordered pair of
vertices are equal. This includes `SimpleGraph` and `Digraph`. -/
class NoParallelEdge (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr]
    [GraphLike V I E Gr] : Prop where
  /-- Two edges linking the same ordered pair of vertices are equal. -/
  edge_eq_of_isLink {G : Gr} {e f : E} {u v : V} :
    IsLink G e u v → IsLink G f u v → e = f

variable [GraphLike V I E Gr] [NoParallelEdge V I E Gr]

lemma IsLink.edge_eq (h : IsLink G e u v) (h' : IsLink G f u v) : e = f :=
  NoParallelEdge.edge_eq_of_isLink h h'

end NoParallelEdge

section Loopless

/-- A graph-like structure is loopless if distinct incidences of the same edge have distinct
endpoints. -/
class Loopless (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
  /-- Distinct incidences of the same edge have distinct endpoints. -/
  no_loops_of_mem_mem ⦃G : Gr⦄ ⦃i j : I⦄ : i ∈ I(G) → j ∈ I(G) → edgeFun G i = edgeFun G j → i ≠ j →
    endPoint G i ≠ endPoint G j

variable [Loopless V I E Gr]

lemma no_loops (hi : i ∈ I(G)) (hij : edgeFun G i = edgeFun G j) (hne : i ≠ j) :
    endPoint G i ≠ endPoint G j := by
  obtain ⟨e, he⟩ := Part.dom_iff_mem.mp (dom_edgeFun G ▸ hi)
  exact Loopless.no_loops_of_mem_mem hi (mem_incs_of_mem_edgeFun (hij ▸ he)) hij hne

lemma no_loops' (hj : j ∈ I(G)) (hij : edgeFun G i = edgeFun G j) (hne : i ≠ j) :
    endPoint G i ≠ endPoint G j := by
  obtain ⟨e, he⟩ := Part.dom_iff_mem.mp (dom_edgeFun G ▸ hj)
  exact Loopless.no_loops_of_mem_mem (mem_incs_of_mem_edgeFun (hij ▸ he)) hj hij hne

lemma IsIncident.inc_inj (hi : IsIncident G i e v) (hj : IsIncident G j e v) : i = j := by
  obtain ⟨hei, hvi⟩ := (mem_edgeFun_mem_endPoint_iff_isIncident ..).mpr hi
  obtain ⟨hej, hvj⟩ := (mem_edgeFun_mem_endPoint_iff_isIncident ..).mpr hj
  exact not_imp_not.mp (no_loops hi.inc_mem (Part.mem_right_unique hei hej))
    (Part.mem_right_unique hvi hvj)

end Loopless

end HyperGraphLike
