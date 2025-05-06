/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
import Mathlib.Data.Set.Basic

/-!
# Multigraphs

A multigraph is a set of vertices and a set of edges,
together with incidence data that associates each edge `e`
with an unordered pair `(x,y)` of vertices called the 'ends' of `e`.
`x` and `y` may be equal, in which case `e` is a 'loop',
and there may also be more than one edge `e` whose ends are the same pair `(x,y)`.
A multigraph where neither of these occurs is 'simple',
and these objects are described by `SimpleGraph`.

This module defines `Graph α ε` for a vertex type `α` and an edge type `ε`,
and gives basic API for incidence, adjacency and extensionality.
The design broadly follows [Chou1994].

## Main definitions

For `G : Graph α ε`, ...

* `G.V` denotes the vertex set of `G` as a term in `Set α`.
* `G.E` denotes the edge set of `G` as a term in `Set ε`.
* `G.Inc₂ e x y` means that the edge `e : ε` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e : ε` has `x` as one of its ends.
* `G.Adj x y` means that there is an edge `e` having `x` and `y` as its ends.
* `G.IsLoopAt e x` means that `e` is a loop edge with both ends equal to `x`.
* `G.IsNonloopAt e x` means that `e` is a non-loop edge with one end equal to `x`.

## Implementation notes

Unlike the design of `SimpleGraph`, the vertex and edge sets of `G` are modelled as sets
`G.V : Set α` and `G.E : Set ε`, within ambient types, rather than being types themselves.
This mimics the 'embedded set' design used in `Matroid`, which seems to be more convenient for
formalizing real-world proofs in combinatorics.

A specific advantage is that this will allow subgraphs of `G : Graph α ε` to also exist on
an equal footing with `G` as terms in `Graph α ε`,
and so there is no need for an extensive `Graph.subgraph` API and all the associated
definitions and canonical coercion maps. The same will go for minors and the various other
partial orders on multigraphs.

The main tradeoff is that parts of the API will require caring about whether a term
`x : α` or `e : ε` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation.

## Notation

Reflecting written mathematics, we use the compact notations `G.V` and `G.E` to describe
vertex and edge sets formally, but use the longer terms `vxSet` and `edgeSet` within
lemma names to refer to the same objects.

-/

variable {α ε : Type*} {x y z u v w : α} {e f : ε}

open Set

/-- A multigraph with vertex set `V : Set α` and edge set `E : Set ε`,
as described by a predicate describing whether an edge `e : ε` has ends `x` and `y`.
For definitional reasons, we include the edge set `E` as a structure field
even though it can be inferred from `Inc₂` via `edge_mem_iff_exists_inc₂`;
see `Graph.mk'` for a constructor that does not use `E`. -/
structure Graph (α ε : Type*) where
  /-- The vertex set. -/
  V : Set α
  /-- The edge set. -/
  E : Set ε
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e` -/
  Inc₂ : ε → α → α → Prop
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  inc₂_symm : ∀ ⦃e⦄, e ∈ E → (Symmetric <| Inc₂ e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_inc₂_of_inc₂ : ∀ ⦃e x y v w⦄, Inc₂ e x y → Inc₂ e v w → x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set -/
  edge_mem_iff_exists_inc₂ : ∀ e, e ∈ E ↔ ∃ x y, Inc₂ e x y
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  vx_mem_left_of_inc₂ : ∀ ⦃e x y⦄, Inc₂ e x y → x ∈ V

namespace Graph

variable {G : Graph α ε}

/-! ### Edge-vertex-vertex incidence -/

lemma Inc₂.edge_mem (h : G.Inc₂ e x y) : e ∈ G.E :=
  (edge_mem_iff_exists_inc₂ ..).2 ⟨x, y, h⟩

lemma Inc₂.symm (h : G.Inc₂ e x y) : G.Inc₂ e y x :=
  G.inc₂_symm h.edge_mem h

lemma Inc₂.vx_mem_left (h : G.Inc₂ e x y) : x ∈ G.V :=
  G.vx_mem_left_of_inc₂ h

lemma Inc₂.vx_mem_right (h : G.Inc₂ e x y) : y ∈ G.V :=
  h.symm.vx_mem_left

lemma inc₂_comm : G.Inc₂ e x y ↔ G.Inc₂ e y x :=
  ⟨Inc₂.symm, Inc₂.symm⟩

lemma exists_inc₂_of_mem_edgeSet (h : e ∈ G.E) : ∃ x y, G.Inc₂ e x y :=
  (edge_mem_iff_exists_inc₂ ..).1 h

lemma edgeSet_eq_setOf_exists_inc₂ : G.E = {e | ∃ x y, G.Inc₂ e x y} :=
  Set.ext fun e ↦ G.edge_mem_iff_exists_inc₂ e

lemma Inc₂.left_eq_or_eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_inc₂_of_inc₂ h h'

lemma Inc₂.left_eq_of_inc₂_of_ne (h : G.Inc₂ e x y) (h' : G.Inc₂ e z w) (hzx : x ≠ z) : x = w :=
  (h.left_eq_or_eq_of_inc₂ h').elim (False.elim ∘ hzx) id

lemma Inc₂.eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e x z) : y = z := by
  obtain rfl | rfl := h.symm.left_eq_or_eq_of_inc₂ h'.symm
  · rfl
  obtain rfl | rfl := h'.symm.left_eq_or_eq_of_inc₂ h.symm <;> rfl

/-! ### Edge-vertex incidence -/

/-- The unary incidence predicate of `G`. `G.Inc e x` means that `x` is one of the ends of `e`. -/
def Inc (G : Graph α ε) (e : ε) (x : α) : Prop := ∃ y, G.Inc₂ e x y

@[simp]
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ G.E :=
  h.choose_spec.edge_mem

@[simp]
lemma Inc.vx_mem (h : G.Inc e x) : x ∈ G.V :=
  h.choose_spec.vx_mem_left

@[simp]
lemma Inc₂.inc_left (h : G.Inc₂ e x y) : G.Inc e x :=
  ⟨y, h⟩

@[simp]
lemma Inc₂.inc_right (h : G.Inc₂ e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

lemma Inc.eq_or_eq_of_inc₂ (h : G.Inc e x) (h' : G.Inc₂ e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq_of_inc₂ h'

lemma Inc.eq_of_inc₂_of_ne_left (h : G.Inc e x) (h' : G.Inc₂ e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_inc₂ h').elim (False.elim ∘ hxy) id

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma inc₂_iff_inc : G.Inc₂ e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_inc₂ h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq_of_inc₂ hy'
    · assumption
    exact hy'.symm
  assumption

/-- Given a proof that `e` is incident with `x`, noncomputably find the other end of `e`.
(If `e` is a loop, this is equal to `x` itself). -/
noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp]
lemma Inc.inc₂_other (h : G.Inc e x) : G.Inc₂ e x h.other :=
  h.choose_spec

@[simp]
lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.inc₂_other.inc_right

lemma Inc.eq_or_eq_or_eq_of_inc_of_inc (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_inc₂_of_ne_left hx' hcon.1.symm
  obtain rfl := hz.eq_of_inc₂_of_ne_left hx' hcon.2.1.symm
  exact hcon.2.2 rfl

/-- `G.IsLoopAt e x` means that both ends of `e` are equal to `x`. -/
def IsLoopAt (G : Graph α ε) (e : ε) (x : α) : Prop := G.Inc₂ e x x

@[simp]
lemma inc₂_self_iff : G.Inc₂ e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  Inc₂.inc_left h

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_inc₂ h <;> rfl

@[simp]
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ G.E :=
  h.inc.edge_mem

@[simp]
lemma IsLoopAt.vx_mem (h : G.IsLoopAt e x) : x ∈ G.V :=
  h.inc.vx_mem

/-- `G.IsNonloopAt e x` means that `e` is an edge from `x` to some `y ≠ x`. -/
@[mk_iff]
structure IsNonloopAt (G : Graph α ε) (e : ε) (x : α) : Prop where
  inc : G.Inc e x
  exists_inc₂_ne : ∃ y ≠ x, G.Inc₂ e x y

@[simp]
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ G.E :=
  h.inc.edge_mem

@[simp]
lemma IsNonloopAt.vx_mem (h : G.IsNonloopAt e x) : x ∈ G.V :=
  h.inc.vx_mem

lemma IsLoopAt.not_isNonloop_at (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  intro h'
  obtain ⟨z, hyz, hy⟩ := h'.exists_inc₂_ne
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloop_at x h

lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  obtain ⟨y, hy⟩ := h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl hy
  exact .inr ⟨hy.inc_left, y, hne.symm, hy⟩

/-! ### Adjacency -/

/-- `G.Adj x y` means that `G` has an edge from `x` to `y`. -/
def Adj (G : Graph α ε) (x y : α) : Prop := ∃ e, G.Inc₂ e x y

lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩

lemma adj_comm : G.Adj x y ↔ G.Adj y x :=
  ⟨Adj.symm, Adj.symm⟩

@[simp]
lemma Adj.mem_left (h : G.Adj x y) : x ∈ G.V :=
  h.choose_spec.vx_mem_left

@[simp]
lemma Adj.mem_right (h : G.Adj x y) : y ∈ G.V :=
  h.symm.mem_left

lemma Inc₂.adj (h : G.Inc₂ e x y) : G.Adj x y :=
  ⟨e, h⟩

/-! ### Extensionality -/

/-- A constructor for `Graph` in which the edge set is inferred from the incidence predicate
rather than supplied explicitly. -/
@[simps]
protected def mk' (V : Set α) (Inc₂ : ε → α → α → Prop)
    (inc₂_symm : ∀ ⦃e x y⦄, Inc₂ e x y → Inc₂ e y x)
    (eq_or_eq_of_inc₂_of_inc₂ : ∀ ⦃e x y v w⦄, Inc₂ e x y → Inc₂ e v w → x = v ∨ x = w)
    (vx_mem_left_of_inc₂ : ∀ ⦃e x y⦄, Inc₂ e x y → x ∈ V) : Graph α ε where
  V := V
  E := {e | ∃ x y, Inc₂ e x y}
  Inc₂ := Inc₂
  inc₂_symm _ _ _ _ h := inc₂_symm h
  eq_or_eq_of_inc₂_of_inc₂ := eq_or_eq_of_inc₂_of_inc₂
  edge_mem_iff_exists_inc₂ _ := Iff.rfl
  vx_mem_left_of_inc₂ := vx_mem_left_of_inc₂

@[simp]
lemma mk'_eq_self (G : Graph α ε) : Graph.mk' G.V G.Inc₂ (fun _ _ _ ↦ Inc₂.symm)
  (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq_of_inc₂ h') (fun _ _ _ ↦ Inc₂.vx_mem_left) = G := by
  have h := G.edgeSet_eq_setOf_exists_inc₂
  cases G with | mk V E Inc₂ _ _ _ => simpa [Graph.mk'] using h.symm

/-- Two graphs with the same vertex set and binary incidences are equal.
(We use this as the default extensionality lemma rather than adding `@[ext]`
to the definition of `Graph`, so it doesn't require equality of the edge sets.) -/
@[ext]
protected lemma ext {G₁ G₂ : Graph α ε} (hV : G₁.V = G₂.V)
    (h : ∀ e x y, G₁.Inc₂ e x y ↔ G₂.Inc₂ e x y) : G₁ = G₂ := by
  rw [← G₁.mk'_eq_self, ← G₂.mk'_eq_self]
  simp_rw [hV]
  convert rfl using 2
  ext
  rw [h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
@[ext]
lemma ext_inc {G₁ G₂ : Graph α ε} (hV : G₁.V = G₂.V) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [inc₂_iff_inc, h]

end Graph
