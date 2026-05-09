/-
Copyright (c) 2025 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith, Bhavik Mehta
-/
module
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card

/-!
# Undirected hypergraphs

An *undirected hypergraph* (here abbreviated as *hypergraph*) `H` is a generalization of a graph
(see `Mathlib.Combinatorics.Graph` or `Mathlib.Combinatorics.SimpleGraph`) and consists of a set of
*vertices*, usually denoted `V` or `V(H)`, and a set of *hyperedges*, here called *edges* and
denoted `E` or `E(H)`. In contrast with a graph, where edges are unordered pairs of vertices, in
hypergraphs, edges are (unordered) sets of vertices; i.e., they are subsets of the vertex set `V`.

A hypergraph where `V = ∅` and `E = ∅` is *empty*. A hypergraph with a nonempty
vertex set (`V ≠ ∅`) and empty edge set is *trivial*.

If a edge `e` contains only one vertex (i.e., `|e| = 1`), then it is a *loop*.

This module defines `Hypergraph α` for a vertex type `α` (edges are defined as `Set (Set α)`).

## Main definitions

For `H : Hypergraph α`:

* `V(H)` denotes the vertex set of `H` as a term in `Set α`.
* `E(H)` denotes the edge set of `H` as a term in `Set (Set α)`. Hyperedges must be subsets of
    `V(H)`.
* `H.Adj x y` means that there exists some edge containing both `x` and `y` (or, in other
    words, `x` and `y` are incident to some shared edge `e`).
* `H.EAdj e f` means that there exists some vertex that is incident to the edges `e` and
    `f : Set α`.

## Implementation details

This implementation is heavily inspired by Peter Nelson and Jun Kwon's `Graph` implementation,
which was in turn inspired by `Matroid`.

Paraphrasing `Mathlib.Combinatorics.Graph.Basic`:
"The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : Set α` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation."

Because `edgeSet` is a `Set (Set α)`, rather than a multiset, here we are assuming that
all hypergraphs are *without repeated edge*.

-/

@[expose] public section

open Set

variable {α β γ : Type*} {x y : α} {e e' f g : Set α} {l : Set (Set α)}

/--
An undirected hypergraph with vertices of type `α` and edges of type `Set α`, as described by vertex
and edge sets `vertexSet : Set α` and `edgeSet : Set (Set α)`.

The requirement `subset_vertexSet_of_mem_edgeSet` ensures that all vertices in edges are part of
`vertexSet`, i.e., all edges are subsets of the `vertexSet`.
-/
@[ext]
structure Hypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The edge set -/
  edgeSet : Set (Set α)
  /-- All edges must be subsets of the vertex set -/
  subset_vertexSet_of_mem_edgeSet' : ∀ ⦃e⦄, e ∈ edgeSet → e ⊆ vertexSet

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `edgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.edgeSet H


/-! ## Vertex-Hyperedge Incidence -/

@[simp]
lemma subset_vertexSet_of_mem_edgeSet (he : e ∈ E(H)) : e ⊆ V(H) :=
  H.subset_vertexSet_of_mem_edgeSet' he

lemma _root_.Membership.mem.subset_vertexSet (he : e ∈ E(H)) : e ⊆ V(H) :=
  H.subset_vertexSet_of_mem_edgeSet he

lemma edgeSet_subset_powerset_vertexSet {H : Hypergraph α} : E(H) ⊆ V(H).powerset := by
  intro e he
  exact he.subset_vertexSet

lemma mem_vertexSet_of_mem_edgeSet (he : e ∈ E(H)) (hx : x ∈ e) : x ∈ V(H) :=
  H.subset_vertexSet_of_mem_edgeSet he hx

lemma edgeSet.ext_iff (he : e ∈ E(H)) (he' : e' ∈ E(H)) : e = e' ↔ ∀ x ∈ V(H), x ∈ e ↔ x ∈ e' :=
  Iff.intro
  (fun a x a_1 ↦ Iff.of_eq (congrFun a x))
  (
    by
    intro h
    refine ext ?_
    intro x
    have h': x ∈ V(H) ∨ x ∉ V(H) := Classical.em (x ∈ V(H))
    cases h' with
    | inl xmem => exact Iff.symm ((fun {a b} ↦ iff_comm.mp) (h x xmem))
    | inr xnmem => (
      refine Iff.symm ((fun {a b} ha ↦ (iff_false_left ha).mpr) ?_ ?_)
      · contrapose xnmem
        exact mem_vertexSet_of_mem_edgeSet he' xnmem
      · contrapose xnmem
        exact mem_vertexSet_of_mem_edgeSet he xnmem
    )
  )

lemma sUnion_edgeSet_subset_vertexSet : ⋃₀ E(H) ⊆ V(H) :=
  subset_powerset_iff.mp edgeSet_subset_powerset_vertexSet

/-! ## Vertex and Hyperedge Adjacency -/

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some edge `e ∈ E(H)`
where `x` and `y` are both incident to `e`.

Note that we do not need to explicitly check that `x, y ∈ V(H)` here because a vertex that is not in
the vertex set cannot be incident to any edge.
-/
def Adj (H : Hypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(H), x ∈ e ∧ y ∈ e

lemma Adj.symm (h : H.Adj x y) : H.Adj y x := by grind [Adj]

lemma adj_comm (x y : α) : H.Adj x y ↔ H.Adj y x := ⟨.symm, .symm⟩

/--
Predicate for edge adjacency. Analogous to `Hypergraph.Adj`, edges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident to both `e` and `f`.
-/
def EAdj (H : Hypergraph α) (e : Set α) (f : Set α) : Prop :=
  e ∈ E(H) ∧ f ∈ E(H) ∧ ∃ x, x ∈ e ∧ x ∈ f

lemma EAdj.exists_vertex (h : H.EAdj e f) : ∃ x ∈ V(H), x ∈ e ∧ x ∈ f := by
  obtain ⟨x, hx⟩ := h.2.2
  exact ⟨x, mem_vertexSet_of_mem_edgeSet h.1 hx.1, hx⟩

lemma EAdj.symm (h : H.EAdj e f) : H.EAdj f e := by grind [EAdj]

lemma EAdj.inter_nonempty (hef : H.EAdj e f) : (e ∩ f).Nonempty :=
  Set.inter_nonempty.mpr hef.2.2

lemma eAdj_comm (e f) : H.EAdj e f ↔ H.EAdj f e := ⟨.symm, .symm⟩

/-! ## Basic Hypergraph Definitions & Predicates-/

/-- The *star* of a vertex `x` is the set of all edges `e ∈ E(H)` incident to `x`. -/
def star (H : Hypergraph α) (x : α) : Set (Set α) := {e ∈ E(H) | x ∈ e}

/-- The *star set* is the set of subsets of `E(H)` of edges incident to a vertex in `V(H)`. -/
def stars (H : Hypergraph α) : Set (Set (Set α)) := {H.star x | x ∈ V(H)}

/-- The *image* of a hypergraph `H : Hypergraph α` under a function `f : α → β` is the hypergraph
`Hᶠ : Hypergraph β` where the vertex set of `Hᶠ` is the image of `V(H)` under `f` and the edge set
of `Hᶠ` is the set of images of the edges (subsets of vertices) in `E(H)`. -/
@[simps]
protected def image (H : Hypergraph α) (f : α → β) : Hypergraph β where
  vertexSet := V(H).image f
  edgeSet := E(H).image (Set.image f)
  subset_vertexSet_of_mem_edgeSet' := by
    rintro - ⟨e, he, rfl⟩
    exact image_mono he.subset_vertexSet

lemma mem_edgeSet_image {f : α → β} {e : Set β} : e ∈ E(H.image f) ↔ ∃ e' ∈ E(H), f '' e' = e :=
  .rfl

lemma image_mem_edgeSet_image {f : α → β} (he : e ∈ E(H)) : e.image f ∈ E(H.image f) :=
  mem_image_of_mem _ he

lemma image_image {f : α → β} {g : β → γ} (H : Hypergraph α) :
  (H.image f).image g = H.image (g ∘ f) := by
  ext <;> simp [Set.image_image]

/-- A vertex is isolated if it is not incident to any edges (including loops). -/
def IsIsolated (H : Hypergraph α) (x : α) : Prop := ∀ e ∈ E(H), x ∉ e

lemma sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated :
  ⋃₀ E(H) = V(H) ↔ ∀ x ∈ V(H), ¬IsIsolated H x := by
    grind [IsIsolated, mem_vertexSet_of_mem_edgeSet]

/-- A loop is an edge whose associated vertex subset consists of a single vertex. -/
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := e ∈ E(H) ∧ ∃ x ∈ V(H), e = {x}

lemma isLoop_iff_mem_and_ncard_one : H.IsLoop e ↔ (e ∈ E(H) ∧ Set.ncard e = 1) :=
  Iff.intro
  (by grind [IsLoop, ncard_eq_one])
  (by grind [IsLoop, ncard_eq_one, mem_vertexSet_of_mem_edgeSet, mem_vertexSet_of_mem_edgeSet])

lemma IsLoop.ncard_one (h : H.IsLoop e) : Set.ncard e = 1 := (isLoop_iff_mem_and_ncard_one.mp h).2

/-- A hypergraph is empty if it has no vertices and no edges. -/
def IsEmpty (H : Hypergraph α) : Prop := V(H) = ∅ ∧ E(H) = ∅

/-- A hypergraph is nonempty if it has at least one vertex and at least one edge. -/
def IsNonempty (H : Hypergraph α) : Prop := (∃ x, x ∈ V(H)) ∨ (∃ e, e ∈ E(H))

/-- The empty hypergraph on a type. -/
@[simps]
def emptyHypergraph (α : Type*) : Hypergraph α where
  vertexSet := ∅
  edgeSet := ∅
  subset_vertexSet_of_mem_edgeSet' := by simp

@[simp]
lemma isNonempty_of_nonempty_vertexSet (hV : V(H).Nonempty) : H.IsNonempty :=
  .inl hV

lemma isEmpty_emptyHypergraph : IsEmpty (emptyHypergraph α) :=
  ⟨rfl, rfl⟩

lemma IsEmpty.eq_emptyHypergraph (h : H.IsEmpty) : H = emptyHypergraph α :=
  Hypergraph.ext_iff.mpr h

lemma IsEmpty.vertexSet_eq (hH : H.IsEmpty) : V(H) = ∅ := hH.1

lemma IsEmpty.edgeSet_eq (hH : H.IsEmpty) : E(H) = ∅ := hH.2

@[simp]
lemma isEmpty_iff_forall_not_mem : H.IsEmpty ↔ (∀ x, x ∉ V(H)) ∧ (∀ e, e ∉ E(H)) := by
   simp_rw [IsEmpty, Set.eq_empty_iff_forall_notMem]

lemma IsEmpty.not_mem_edgeSet (hH : H.IsEmpty) {e : Set α} : e ∉ E(H) := by
  unfold IsEmpty at hH
  grind

lemma notMem_edgeSet_emptyHypergraph : e ∉ E(emptyHypergraph α) :=
  IsEmpty.not_mem_edgeSet isEmpty_emptyHypergraph

lemma not_isEmpty_iff : ¬H.IsEmpty ↔ H.IsNonempty := by grind [IsEmpty, IsNonempty]

lemma not_isNonempty : ¬H.IsNonempty ↔ H.IsEmpty := not_iff_comm.mp not_isEmpty_iff

alias ⟨_, IsEmpty.not_isNonempty⟩ := not_isNonempty
alias ⟨_, IsNonempty.not_isEmpty⟩ := not_isEmpty_iff

variable (H) in
lemma isEmpty_or_isNonempty : H.IsEmpty ∨ H.IsNonempty := by grind [IsEmpty, IsNonempty]

/-- A hypergraph is trivial if it has at least one vertex but no edges. -/
def IsTrivial (H : Hypergraph α) : Prop := Set.Nonempty V(H) ∧ E(H) = ∅

/-- The trivial hypergraph with a given vertex set. -/
@[simps]
def trivialHypergraph (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := ∅
  subset_vertexSet_of_mem_edgeSet' := by simp

lemma IsTrivial.not_isEmpty (hh : IsTrivial H) : ¬IsEmpty H := by
  grind [IsEmpty, IsTrivial, Set.nonempty_iff_ne_empty]

lemma IsTrivial.not_mem_edgeSet (h : H.IsTrivial) : e ∉ E(H) := by grind [IsTrivial]

/-- A hypergraph is complete if every subset of the vertex set is in the edge set. -/
def IsComplete (H : Hypergraph α) : Prop := ∀ e ⊆ V(H), e ∈ E(H)

/-- The complete hypergraph with a given vertex set. -/
@[simps]
def completeOn (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := 𝒫 f
  subset_vertexSet_of_mem_edgeSet' := by simp

lemma mem_completeOn : e ∈ E(completeOn f) ↔ e ⊆ f := by simp

lemma isComplete_completeOn (f : Set α) : (completeOn f).IsComplete := fun _ a ↦ a

lemma IsComplete.isNonempty (h : H.IsComplete) : H.IsNonempty :=
  Or.inr ⟨∅, h ∅ (Set.empty_subset _)⟩

lemma IsComplete.not_isEmpty (h : H.IsComplete) : ¬ H.IsEmpty :=
  H.not_isEmpty_iff.mpr h.isNonempty

lemma IsComplete.not_isTrivial (h : H.IsComplete) : ¬H.IsTrivial := by
  intro hH
  exact hH.not_mem_edgeSet (e := ∅) (h ∅ (Set.empty_subset _))

lemma completeOn_not_isTrivial {S : Set α} : ¬(completeOn S).IsTrivial := by
  unfold IsTrivial
  apply not_and_or.mpr
  right
  exact ne_of_mem_of_not_mem' (fun ⦃a⦄ a ↦ a) fun a ↦ a

end Hypergraph
