/-
Copyright (c) 2026 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
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
hypergraphs, edges are unordered sets of vertices; i.e., they are subsets of the vertex set `V`.

A hypergraph where `V = ∅` and `E = ∅` is *empty*, denoted `⊥`. A hypergraph with a nonempty
vertex set (`V ≠ ∅`) and empty edge set is *trivial*. A hypergraph where the edge set is the power
set of the vertex set (or, equivalently, where all possible subsets of the vertex sets are in the
edge set) is *complete*.

If a edge `e` contains only one vertex (i.e., `|e| = 1`), then it is a *loop*.

This module defines `Hypergraph α` for a vertex type `α` (edges are defined as `Set (Set α)`).

## Main definitions

* `Hypergraph α` is the type of undirected hypergraphs with vertices of type `α` and edges of type
  `Set α`. In addition to vertices and hyperedges, a `Hypergraph` must have the property that all
  edges are subsets of the vertex set.

For `H : Hypergraph α`:

* `H.vertexSet` (abbrev. `V(H)`) denotes the vertex set of `H` as a term in `Set α`.
* `H.edgeSet` (abbrev. `E(H)`) denotes the edge set of `H` as a term in `Set (Set α)`. Hyperedges
  must be subsets of `V(H)`.
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

public section

open Set

variable {α β γ : Type*} {x y : α} {e e' f : Set α}

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

alias _root_.Membership.mem.subset_vertexSet := subset_vertexSet_of_mem_edgeSet

lemma edgeSet_subset_powerset_vertexSet {H : Hypergraph α} : E(H) ⊆ V(H).powerset :=
  fun _ ↦ subset_vertexSet_of_mem_edgeSet

lemma mem_vertexSet_of_mem_edgeSet (he : e ∈ E(H)) (hx : x ∈ e) : x ∈ V(H) :=
  H.subset_vertexSet_of_mem_edgeSet he hx

lemma edgeSet.ext_iff (he : e ∈ E(H)) (he' : e' ∈ E(H)) : e = e' ↔ ∀ x ∈ V(H), x ∈ e ↔ x ∈ e' := by
  grind [he.subset_vertexSet, he'.subset_vertexSet]

lemma sUnion_edgeSet_subset_vertexSet : ⋃₀ E(H) ⊆ V(H) :=
  subset_powerset_iff.mp edgeSet_subset_powerset_vertexSet

/-! ## Vertex and Hyperedge Adjacency -/

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some edge `e ∈ E(H)`
where `x` and `y` are both incident to `e`.

Note that we do not need to explicitly check that `x, y ∈ V(H)` here because a vertex that is not in
the vertex set cannot be incident to any edge.
-/
@[expose]
def Adj (H : Hypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(H), x ∈ e ∧ y ∈ e

lemma Adj.symm (h : H.Adj x y) : H.Adj y x := by grind [Adj]

lemma adj_comm (x y : α) : H.Adj x y ↔ H.Adj y x := ⟨.symm, .symm⟩

/--
Predicate for edge adjacency. Analogous to `Hypergraph.Adj`, edges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident to both `e` and `f`.
-/
@[expose]
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

/-- The *image* of a hypergraph `H : Hypergraph α` under a function `f : α → β` is the hypergraph
`Hᶠ : Hypergraph β` where the vertex set of `Hᶠ` is the image of `V(H)` under `f` and the edge set
of `Hᶠ` is the set of images of the edges (subsets of vertices) in `E(H)`. -/
@[simps, expose]
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
@[expose]
def IsIsolated (H : Hypergraph α) (x : α) : Prop := ∀ e ∈ E(H), x ∉ e

lemma sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated :
    ⋃₀ E(H) = V(H) ↔ ∀ x ∈ V(H), ¬IsIsolated H x := by
  grind [IsIsolated, mem_vertexSet_of_mem_edgeSet]

/-- A loop is an edge whose associated vertex subset consists of a single vertex. -/
@[expose]
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := e ∈ E(H) ∧ ∃ x, e = {x}

lemma isLoop_iff_mem_edgeSet_and_singleton : H.IsLoop e ↔ (e ∈ E(H) ∧ ∃ x, e = {x}) := .rfl

lemma isLoop_iff_mem_and_ncard_one : H.IsLoop e ↔ (e ∈ E(H) ∧ Set.ncard e = 1) := by
  grind [IsLoop, ncard_eq_one, mem_vertexSet_of_mem_edgeSet]

lemma IsLoop.ncard_one (h : H.IsLoop e) : Set.ncard e = 1 := (isLoop_iff_mem_and_ncard_one.mp h).2

/-- A hypergraph is nonempty if it has at least one vertex or at least one edge. -/
@[expose]
def IsNonempty (H : Hypergraph α) : Prop := V(H).Nonempty ∨ E(H).Nonempty

/-- The empty hypergraph (bottom) on a type. -/
@[simps]
instance (α : Type*) : Bot (Hypergraph α) where
  bot.vertexSet := ∅
  bot.edgeSet := ∅
  bot.subset_vertexSet_of_mem_edgeSet' := by simp

@[simp]
lemma IsNonempty.of_nonempty_vertexSet (hV : V(H).Nonempty) : H.IsNonempty :=
  .inl hV

@[simp]
lemma IsNonempty.of_nonempty_edgeSet (hE : E(H).Nonempty) : H.IsNonempty :=
  .inr hE

@[simp]
theorem ne_bot_iff : H ≠ ⊥ ↔ H.IsNonempty := by
  simp [IsNonempty, Set.nonempty_iff_ne_empty, Hypergraph.ext_iff]
  grind [bot_vertexSet, bot_edgeSet]

alias ⟨_, IsNonempty.ne_bot⟩ := ne_bot_iff

@[simp]
theorem not_isNonempty_iff : ¬H.IsNonempty ↔ H = ⊥ :=
  not_iff_comm.mp ne_bot_iff

variable (H) in
lemma eq_bot_or_isNonempty : H = ⊥ ∨ H.IsNonempty := by
  have h : (V(H) = ∅ ∧ E(H) = ∅) ∨ (V(H).Nonempty ∨ E(H).Nonempty) := by grind [Set.Nonempty]
  cases h with
  | inl empty => (
    left
    apply Hypergraph.ext empty.1 empty.2
  )
  | inr nonempty => (
    right
    grind [IsNonempty]
  )

/-- A hypergraph is trivial if it has at least one vertex but no edges. -/
@[expose]
def IsTrivial (H : Hypergraph α) : Prop := Set.Nonempty V(H) ∧ E(H) = ∅

/-- The trivial hypergraph with a given vertex set is defined by having no edges on that vertex
set. -/
@[simps, expose]
def trivialOn (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := ∅
  subset_vertexSet_of_mem_edgeSet' := by simp

lemma IsTrivial.trivialOn (hf : Set.Nonempty f) :
    IsTrivial (trivialOn f) := by
  grind [trivialOn, IsTrivial]

lemma IsTrivial.isNonempty (h : IsTrivial H) : IsNonempty H := by
  grind [IsNonempty, IsTrivial, Set.nonempty_iff_ne_empty]

lemma IsTrivial.not_mem_edgeSet (h : H.IsTrivial) : e ∉ E(H) := by grind [IsTrivial]

/-- A hypergraph is complete if every subset of the vertex set is in the edge set. -/
@[expose]
def IsComplete (H : Hypergraph α) : Prop := ∀ e ⊆ V(H), e ∈ E(H)

/-- The complete hypergraph with a given vertex set, which has each subset of the vertex set as an
edge. -/
@[simps, expose]
def completeOn (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := 𝒫 f
  subset_vertexSet_of_mem_edgeSet' := by simp

lemma mem_completeOn : e ∈ E(completeOn f) ↔ e ⊆ f := by simp

lemma IsComplete.mem_iff (h : H.IsComplete) : e ∈ E(H) ↔ e ⊆ V(H) := by
  grind [IsComplete, subset_vertexSet_of_mem_edgeSet]

lemma IsComplete.completeOn (f : Set α) : (completeOn f).IsComplete := fun _ a ↦ a

lemma IsComplete.isNonempty (h : H.IsComplete) : H.IsNonempty :=
  Or.inr ⟨∅, h ∅ (Set.empty_subset _)⟩

lemma IsComplete.not_isTrivial (h : H.IsComplete) : ¬ H.IsTrivial := by
  intro hH
  exact hH.not_mem_edgeSet (h ∅ (Set.empty_subset _))

lemma not_isTrivial_completeOn (f : Set α) : ¬ (completeOn f).IsTrivial :=
  (IsComplete.completeOn f).not_isTrivial

end Hypergraph
