/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.PFun
public import Mathlib.Order.Partition.Basic

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `GraphLike` for capturing the common structure of different kinds
of graph structures including `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `HyperGraphLike`: is the main typeclass for capturing the common notion of hypergraphs.
  The field `verts` gives the set of vertices of a graph-like structure,
  the field `darts` gives the set of darts, which is an oriented edge, of a graph-like structure,
  the field `edges` gives the set of edges of a graph-like structure,
  and the field `Adj` gives the adjacency relation between vertices.
* `GraphLike`: is the typeclass for graph-like structures where each edge has order 2 and among the
  two incidences, at least one is a source and the other is a target.
* `Undirected`: is the typeclass for undirected graph-like structures, that is every incidence is
  both a source and a target.
* `Directed`: is the typeclass for directed graph-like structures, that is no incidence is both a
  source and a target.
* `NoMultiEdge`: is the typeclass for graph-like structures where no two edges have same sort of
  incidence to the same set of vertices.
* `Loopless`: is the typeclass for graph-like structures where no edge has more than one incidence
  to a vertex.

-/

public section

open Set Function

/-- The `GraphLike` typeclass abstracts over graph-like structures including hypergraphs.
It has vertex and edge sets so subgraph relations can be handled within the same type.
The "darts" terminology comes from combinatorial maps, and they are also known as "half-edges" or
"bonds." They represents the ways an edge can be traversed: if `d` is a dart with `edge d = e`,
`source d = u` and `target d = v` then `d` is walk of length 1 from `u` to `v` with edge `e`. In an
undirected graph, each edge is composed of two darts.
`Adj` is the adjacency relation of a graph-like structure. Two vertices, `u` & `v`, are adjacent iff
there is a dart between them and therefore there is an edge that can be traversed from `u` to `v`.
(See `exists_darts_iff_adj`.) -/
class HyperGraphLike (V I E : outParam Type*) (Gr : Type*) where
  /-- The set of vertices of a graph-like structure. -/
  verts : Gr → Set V
  /-- The set of edges of a graph-like structure. -/
  edges : Gr → Set E
  /-- The relation between an incident object, an edge, and a vertex. -/
  IsIncident : Gr → I → E → V → Prop
  /-- The predicate for being a source incidence. (i.e. incidenct vertex is a source of the incident
  edge) An undirected edge is an edge where all its incidences are both source and targets. -/
  IsSource : Gr → I → Prop
  /-- The predicate for being a target incidence. (i.e. incidenct vertex is a target of the incident
  edge) An undirected edge is an edge where all its incidences are both source and targets. -/
  IsTarget : Gr → I → Prop
  vert_mem_of_isIncident ⦃G i e v⦄ : IsIncident G i e v → v ∈ verts G
  edge_mem_of_isIncident ⦃G i e v⦄ : IsIncident G i e v → e ∈ edges G
  eq_and_eq_of_isIncident_of_isIncident ⦃G i e f u v⦄ :
    IsIncident G i e u → IsIncident G i f v → e = f ∧ u = v
  isIncident_iff ⦃G i⦄ : (∃ e v, IsIncident G i e v) ↔ IsSource G i ∨ IsTarget G i
  -- Following fields are included for defEq
  /-- The set of incident objects of a graph-like structure. -/
  incs : Gr → Set I := fun G ↦ {i | ∃ e v, IsIncident G i e v}
  incs_def ⦃G⦄ : incs G = {i | ∃ e v, IsIncident G i e v} := by grind
  /-- The predicate for an edge being a link of two vertices. -/
  IsLink : Gr → E → V → V → Prop := fun G e u v ↦ ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧
    IsIncident G i e u ∧ IsIncident G j e v
  isLink_def ⦃G e u v⦄ : IsLink G e u v ↔
    ∃ i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧ IsIncident G i e u ∧ IsIncident G j e v := by grind
  /-- The adjacency relation of a graph-like structure. -/
  Adj : Gr → V → V → Prop := fun G u v ↦ ∃ e i j, i ≠ j ∧ IsSource G i ∧ IsTarget G j ∧
    IsIncident G i e u ∧ IsIncident G j e v
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

variable {V I E Gr R : Type*} {G : Gr} [HyperGraphLike V I E Gr] {u u' v v' w : V} {i j : I}
  {e f : E} [AddMonoid R] {l m n : R}

section HyperGraphLike

lemma IsSource.mem (h : IsSource G i) : i ∈ I(G) := by
  rw [incs_def, mem_setOf_eq, isIncident_iff]
  exact Or.inl h

lemma IsTarget.mem (h : IsTarget G i) : i ∈ I(G) := by
  rw [incs_def, mem_setOf_eq, isIncident_iff]
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
  simp only [incs_def, mem_setOf_eq, not_exists, Pi.bot_apply, «Prop».bot_eq_false,
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
  simp [← ((isIncident_edgeFun_endPoint h.inc_mem).inj h).1]

@[grind →]
lemma IsIncident.mem_endPoint (h : IsIncident G i e v) : v ∈ endPoint G i := by
  simp [← ((isIncident_edgeFun_endPoint h.inc_mem).inj h).2]

@[simp, grind =]
lemma mem_edgeFun_iff_exists_isIncident (G : Gr) (e : E) (i : I) :
    e ∈ edgeFun G i ↔ ∃ v, IsIncident G i e v := by
  refine ⟨fun hei ↦ ?_, fun ⟨v, hei⟩ ↦ hei.mem_edgeFun⟩
  have := isIncident_edgeFun_endPoint (mem_incs_of_mem_edgeFun hei)
  rw [PFun.fn_apply, Part.get_eq_of_mem hei] at this
  use (endPoint G).fn i ?_, this

@[simp, grind =]
lemma mem_endPoint_iff_exists_isIncident (G : Gr) (i : I) (v : V) :
    v ∈ endPoint G i ↔ ∃ e, IsIncident G i e v := by
  refine ⟨fun hvi ↦ ?_, fun ⟨e, hei⟩ ↦ hei.mem_endPoint⟩
  have := isIncident_edgeFun_endPoint (mem_incs_of_mem_endPoint hvi)
  rw [(endPoint G).fn_apply, Part.get_eq_of_mem hvi] at this
  use (edgeFun G).fn i ?_, this

@[grind =]
lemma mem_edgeFun_mem_endPoint_iff_isIncident (G : Gr) (i : I) (e : E) (v : V) :
    e ∈ edgeFun G i ∧ v ∈ endPoint G i ↔ IsIncident G i e v := by
  refine ⟨fun ⟨hei, hvi⟩ ↦ ?_, fun h ↦ ⟨h.mem_edgeFun, h.mem_endPoint⟩⟩
  have := isIncident_edgeFun_endPoint (mem_incs_of_mem_edgeFun hei)
  rwa [PFun.fn_apply, PFun.fn_apply, Part.get_eq_of_mem hei, Part.get_eq_of_mem hvi] at this

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

/-- The ENat-valued incidence matrix of a hypergraph-like structure. -/
noncomputable def incMatrix (G : Gr) (l m n : ℕ∞) : Matrix V E ℕ∞ := .of fun v e ↦
  ({i | IsIncident G i e v ∧ IsSource G i ∧ ¬ IsTarget G i}).encard * l +
  ({i | IsIncident G i e v ∧ IsTarget G i ∧ ¬ IsSource G i}).encard * m +
  ({i | IsIncident G i e v ∧ IsSource G i ∧ IsTarget G i}).encard * n

lemma incMatrix_same_apply (G : Gr) (n : ℕ∞) (v : V) (e : E) :
    incMatrix G n n n v e = ({i | IsIncident G i e v}).encard * n := by
  let s : Set I := {i | IsIncident G i e v ∧ IsSource G i ∧ ¬ IsTarget G i}
  let t : Set I := {i | IsIncident G i e v ∧ IsTarget G i ∧ ¬ IsSource G i}
  let b : Set I := {i | IsIncident G i e v ∧ IsSource G i ∧ IsTarget G i}
  have hst : Disjoint s t := by grind
  have hsbt : Disjoint (s ∪ t) b := by grind
  have hpart : {i | IsIncident G i e v} = s ∪ t ∪ b := Set.ext <| by grind
  change s.encard * n + t.encard * n + b.encard * n = ({i | IsIncident G i e v}).encard * n
  rw [hpart, Set.encard_union_eq hsbt, Set.encard_union_eq hst]
  grind

/-- The incidence matrix of a hypergraph-like structure represented by `AddMonoidWithOne`. If the
incidence is `∞`, then the entry is `0`. It is most often used as `incMatrixWith R (-1 : ℤ) 1 1`. -/
noncomputable def incMatrixWith (G : Gr) (l m n : R) : Matrix V E R :=
  .of fun v e ↦ ({i | IsIncident G i e v ∧ IsSource G i ∧ ¬ IsTarget G i}).ncard • l +
    ({i | IsIncident G i e v ∧ IsTarget G i ∧ ¬ IsSource G i}).ncard • m +
    ({i | IsIncident G i e v ∧ IsSource G i ∧ IsTarget G i}).ncard • n

end HyperGraphLike

section GraphLike

/-- A graph-like structure is a hypergraph-like structure where every edge has order 2 and at least
one source and one target incidence. -/
class GraphLike (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
  order_eq_two ⦃G : Gr⦄ ⦃e : E⦄ : e ∈ E(G) → order G e = 2
  exists_isSource_of_mem_edgeSet ⦃G : Gr⦄ ⦃e : E⦄ : e ∈ E(G) → ∃ i, e ∈ edgeFun G i ∧ IsSource G i
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

lemma IsLink.incMatrix_col_eq [DecidableEq V] {n : ℕ∞} (h : IsLink G e u v) :
    (incMatrix G n n n).col e = Pi.single u n + Pi.single v n := by
  obtain ⟨i, j, hij, hi, hj, hi', hj'⟩ := isLink_def.mp h
  obtain ⟨i', j', hne, hpair⟩ := exists_pair_mem_edgeFun_iff hi'.edge_mem
  ext w
  simp only [Matrix.col_apply, incMatrix_same_apply, Pi.add_apply, Pi.single_apply]
  split_ifs with hw₁ hw₂ hw₂
  · simp [show {i | IsIncident G i e w} = {i, j} by grind, encard_pair hij, two_mul]
  · simp [show {i | IsIncident G i e w} = {i} by grind, encard_singleton]
  · simp [show {i | IsIncident G i e w} = {j} by grind, encard_singleton]
  · simp [show {i | IsIncident G i e w} = ∅ by grind, encard_empty]

lemma edgeFun_preimage_singleton_injOn_of_GraphLike : InjOn ((edgeFun G) |>.preimage {·}) E(G) :=
  edgeFun_preimage_singleton_injOn (G := G) fun e he ↦ by simp [order_eq_two he]

end GraphLike

section Undirected

/-- A graph-like structure is undirected if every incidence is both a source and a target. -/
class Undirected (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
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

lemma incMatrixWith_apply_of_undirected (G : Gr) (l m n : R) (v : V) (e : E) :
    incMatrixWith G l m n v e = ({i | IsIncident G i e v}).ncard • n := by
  have h : {i | IsIncident G i e v ∧ IsTarget G i} = {i | IsIncident G i e v} := Set.ext <|
      fun i ↦ ⟨And.left, fun hi ↦ ⟨hi, hi.isSource_or_isTarget.elim ((isSource_iff G i).mp) id⟩⟩
  simp [incMatrixWith, h]

instance : Std.Symm (Adj G) where
  symm _ _ h := by grind [adj_def]

@[symm] lemma Adj.symm (h : Adj G v w) : Adj G w v := symm_of (Adj G) h

lemma adj_comm : Adj G v w ↔ Adj G w v := ⟨symm_of (Adj G), symm_of (Adj G)⟩

lemma IsLink.incMatrixWith_col_eq_of_undirected [GraphLike V I E Gr] [DecidableEq V]
    (h : IsLink G e u v) : (incMatrixWith G l m n).col e = Pi.single u n + Pi.single v n := by
  obtain ⟨i, j, hij, hi, hj, hi', hj'⟩ := isLink_def.mp h
  obtain ⟨i', j', hne, hpair⟩ := exists_pair_mem_edgeFun_iff hi'.edge_mem
  ext w
  simp only [Matrix.col_apply, incMatrixWith_apply_of_undirected, Pi.add_apply, Pi.single_apply]
  split_ifs with hw₁ hw₂ hw₂
  · rw [(show {i | IsIncident G i e w} = {i, j} by grind), ncard_pair hij]
    simp [two_nsmul]
  · simp [show {i | IsIncident G i e w} = {i} by grind]
  · simp [show {i | IsIncident G i e w} = {j} by grind]
  · simp [show {i | IsIncident G i e w} = ∅ by grind]

end Undirected

section Directed

/-- A graph-like structure is directed if no incidence is both a source and a target. -/
class Directed (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
  not_isTarget_of_isSource ⦃G : Gr⦄ ⦃i : I⦄ : IsSource G i → ¬ IsTarget G i
  not_isSource_of_isTarget ⦃G : Gr⦄ ⦃i : I⦄ : IsTarget G i → ¬ IsSource G i

variable [Directed V I E Gr]

@[grind →]
lemma IsSource.not_isTarget (h : IsSource G i) : ¬ IsTarget G i :=
  Directed.not_isTarget_of_isSource h

@[grind →]
lemma IsTarget.not_isSource (h : IsTarget G i) : ¬ IsSource G i :=
  Directed.not_isSource_of_isTarget h

lemma incMatrixWith_apply_of_directed (G : Gr) (l m n : R) (v : V) (e : E) :
    incMatrixWith G l m n v e = ({i | IsIncident G i e v ∧ IsSource G i}).ncard • l +
    ({i | IsIncident G i e v ∧ IsTarget G i}).ncard • m := by
  have hs : {i | IsIncident G i e v ∧ IsSource G i ∧ ¬ IsTarget G i} =
      {i | IsIncident G i e v ∧ IsSource G i} :=
    Set.ext fun x ↦ ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, h.2.not_isTarget⟩⟩
  have ht : {i | IsIncident G i e v ∧ IsTarget G i ∧ ¬ IsSource G i} =
      {i | IsIncident G i e v ∧ IsTarget G i} :=
    Set.ext fun x ↦ ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, h.2.not_isSource⟩⟩
  have hb : {i | IsIncident G i e v ∧ IsSource G i ∧ IsTarget G i} = ∅ :=
    Set.ext fun i ↦ by grind
  simp [incMatrixWith, hs, ht, hb]

lemma IsLink.incMatrixWith_col_eq_of_directed [GraphLike V I E Gr] [DecidableEq V]
    (h : IsLink G e u v) : (incMatrixWith G l m n).col e = Pi.single u l + Pi.single v m := by
  obtain ⟨i, j, hij, hi, hj, hi', hj'⟩ := isLink_def.mp h
  obtain ⟨i', j', hne, hpair⟩ := exists_pair_mem_edgeFun_iff hi'.edge_mem
  ext w
  simp only [Matrix.col_apply, incMatrixWith_apply_of_directed, Pi.add_apply, Pi.single_apply]
  let s := {k | IsIncident G k e w ∧ IsSource G k}
  let t := {k | IsIncident G k e w ∧ IsTarget G k}
  change s.ncard • l + t.ncard • m = _
  split_ifs with hw₁ hw₂ hw₂
  · simp [show s = {i} by grind, show t = {j} by grind]
  · simp [show s = {i} by grind, show t = ∅ by grind]
  · simp [show s = ∅ by grind, show t = {j} by grind]
  · simp [show s = ∅ by grind, show t = ∅ by grind]

end Directed

section NoMultiEdge

/-
### GraphLike with no multi-edge

Some graph-like structures, such as `SimpleGraph` and `Digraph`, does not allow multiple darts/edges
between the same pair of vertices. This section defines a typeclass `NoMultiEdgeGraphLike` for such
graph-like structures.
By the definition of `incMatrixWith`, this definition does not behave well when there are multiple
edges each with infinte incidences.
-/

/-- A graph-like structure with no multi-edge. This includes `SimpleGraph` and `Digraph`. -/
class NoMultiEdge (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
  protected col_inj (G : Gr) : InjOn (incMatrixWith (R := Fin 3 → ℕ) G (Pi.single 0 1)
    (Pi.single 1 1) (Pi.single 2 1)).col E(G)

variable [NoMultiEdge V I E Gr]

lemma IsLink.edge_inj_of_isLink_of_undirected [GraphLike V I E Gr] [Undirected V I E Gr]
    (h : IsLink G e u v) (h' : IsLink G f u v) : e = f :=
  letI := Classical.decEq V
  (NoMultiEdge.col_inj G).eq_iff h.edge_mem h'.edge_mem |>.mp <|
    by rw [h.incMatrixWith_col_eq_of_undirected, h'.incMatrixWith_col_eq_of_undirected]

lemma IsLink.edge_inj_of_isLink_of_directed [GraphLike V I E Gr] [Directed V I E Gr]
    (h : IsLink G e u v) (h' : IsLink G f u v) : e = f :=
  letI := Classical.decEq V
  (NoMultiEdge.col_inj G).eq_iff h.edge_mem h'.edge_mem |>.mp <|
    by rw [h.incMatrixWith_col_eq_of_directed, h'.incMatrixWith_col_eq_of_directed]

end NoMultiEdge

section Loopless

/-- A graph-like structure is loopless if no edge has more than one incidence to a vertex. -/
class Loopless (V I E : outParam Type*) (Gr : Type*) [HyperGraphLike V I E Gr] where
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
