/-
Copyright (c) 2026 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
module
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card

/-!
# Directed hypergraphs

A *directed hypergraph* (here abbreviated as *dihypergraph*) `Dₕ` is a generalization of a directed
graph (see `Mathlib.Combinatorics.Digraph`). It consists of a set of vertices, denoted `V` or
`V(Dₕ)`, and a set of *directed (hyper)edges* (sometimes called *hyperarcs*), denoted `E` or
`E(Dₕ)`. Note that, when we refer to *edges* in this module, we are referring to directed edges
unless otherwise specified.  While, in a digraph, directed edges connect pairs of vertices,
directed edges in a dihypergraph can connect arbitrary numbers of vertices.

This module defines `Dihypergraph α` for a vertex type `α`. We represent an edge `e`
as a pair of sets of vertices (i.e., `e : (Set α) × (Set α)`). Each of the two sets in a directed
edge is called a *side* or a *limb*. The first side is called the *source* or the *tail*, and
the second side is called the *destination* or *head* of the edge.

## Main definitions

* `Dihypergraph α` is the type of dihypergraphs with vertices of type `α` and edges of type
  `(Set α × Set α)`. In addition to vertices and edges, a `Dihypergraph` must have the property
  that the sources and the destinations of all its edges are subsets of the vertex set.

For `Dₕ : Dihypergraph α`:

* `Dₕ.vertexSet` (abbrev. `V(Dₕ)`) denotes the vertex set of `Dₕ` as a term in `Set α`.
* `Dₕ.edgeSet` (abbrev. `E(Dₕ)`) denotes the edge set of `Dₕ` as a term in `((Set α) × (Set α))`.
* `Dₕ.EAdj e f` means that there exists some vertex that is in the destination of `e` and in the
  source of `f`.

## Implementation details

Because `edgeSet` is a `Set((Set α) × (Set α))` rather than a multiset, here we are assuming that
all dihypergraphs are *without repeated edge*. Further, a vertex cannot be present in an edge more
than once.
-/

public section

open Set

variable {α : Type*} {x y z : α} {d d' s s' : Set α} {e f g : (Set α) × (Set α)}

/--
A dihypergraph with vertices of type `α` and edges of type `((Set α) × (Set α))`, as
described by vertex and edge sets `vertexSet : Set α` and `edgeSet : Set ((Set α) × (Set α))`.

The requirement `subset_vertexSet_of_src_dst_of_mem_edgeSet` ensures that, for all edges, all
vertices in the source and all vertices in the destination are part of `vertexSet`, i.e., all
limbs of all edges are subsets of the `vertexSet`.
-/
@[ext]
structure Dihypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The edge set -/
  edgeSet : Set ((Set α) × (Set α))
  /-- Each edge is a pair (s, d), where s ⊆ vertexSet and d ⊆ vertexSet -/
  subset_vertexSet_of_src_dst_of_mem_edgeSet' : (
    ∀ ⦃e⦄, e ∈ edgeSet → e.1 ⊆ vertexSet ∧ e.2 ⊆ vertexSet
  )

namespace Dihypergraph

variable {Dₕ Dₕ' : Dihypergraph α}

/-! ## Notation -/

/-- `V(Dₕ)` denotes the `vertexSet` of a dihypergraph `Dₕ` -/
scoped notation "V(" Dₕ ")" => Dihypergraph.vertexSet Dₕ

/-- `E(Dₕ)` denotes the `edgeSet` of a hypergraph `Dₕ` -/
scoped notation "E(" Dₕ ")" => Dihypergraph.edgeSet Dₕ

/-! ## Dihypergraph Basics -/

lemma subset_vertexSet_of_src_dst_of_mem_edgeSet (he : e ∈ E(Dₕ)) : e.1 ⊆ V(Dₕ) ∧ e.2 ⊆ V(Dₕ) :=
  Dₕ.subset_vertexSet_of_src_dst_of_mem_edgeSet' he

@[simp]
lemma src_isSubset_vertexSet (he : e ∈ E(Dₕ)) : e.1 ⊆ V(Dₕ) :=
  (Dₕ.subset_vertexSet_of_src_dst_of_mem_edgeSet he).1

@[simp]
lemma dst_isSubset_vertexSet (he : e ∈ E(Dₕ)) : e.2 ⊆ V(Dₕ) :=
  (Dₕ.subset_vertexSet_of_src_dst_of_mem_edgeSet he).2

alias _root_.Membership.mem.src_subset_vertexSet := src_isSubset_vertexSet

alias _root_.Membership.mem.dst_subset_vertexSet := dst_isSubset_vertexSet

lemma edgeSet_subset_powerset_vertexSet_vertexSet {Dₕ : Dihypergraph α} :
  E(Dₕ) ⊆ (V(Dₕ).powerset ×ˢ V(Dₕ).powerset) := by
    intro e he
    grind [subset_vertexSet_of_src_dst_of_mem_edgeSet]

/-! ## Vertex-Edge Incidence -/

lemma mem_vertexSet_of_mem_edgeSet_src_dst (he : e ∈ E(Dₕ)) (hx : x ∈ e.1 ∨ x ∈ e.2) : x ∈ V(Dₕ) :=
  by
    cases hx with
    | inl hsrc => apply Set.mem_of_subset_of_mem (src_isSubset_vertexSet he) hsrc
    | inr hdst => apply Set.mem_of_subset_of_mem (dst_isSubset_vertexSet he) hdst

lemma mem_vertexSet_of_mem_edgeSet_src (he : e ∈ E(Dₕ)) (hx : x ∈ e.1) : x ∈ V(Dₕ) :=
  Dₕ.src_isSubset_vertexSet he hx

lemma mem_vertexSet_of_mem_edgeSet_dst (he : e ∈ E(Dₕ)) (hx : x ∈ e.2) : x ∈ V(Dₕ) :=
  Dₕ.dst_isSubset_vertexSet he hx

lemma edgeSet.src_ext_iff (he : e ∈ E(Dₕ)) (hf : f ∈ E(Dₕ)) :
  e.1 = f.1 ↔ ∀ x ∈ V(Dₕ), (x ∈ e.1 ↔ x ∈ f.1) := by
    grind [he.src_subset_vertexSet, hf.src_subset_vertexSet]

lemma edgeSet.dst_ext_iff (he : e ∈ E(Dₕ)) (hf : f ∈ E(Dₕ)) :
  e.2 = f.2 ↔ ∀ x ∈ V(Dₕ), (x ∈ e.2 ↔ x ∈ f.2) := by
    grind [he.dst_subset_vertexSet, hf.dst_subset_vertexSet]

lemma edgeSet.ext_iff (he : e ∈ E(Dₕ)) (hf : f ∈ E(Dₕ)) :
  e = f ↔ ∀ x ∈ V(Dₕ), (x ∈ e.1 ↔ x ∈ f.1) ∧ (x ∈ e.2 ↔ x ∈ f.2) := by
  grind [src_ext_iff, dst_ext_iff]

/--
The *source star* of a vertex `x` is the set of all sources of edges `e ∈ E(Dₕ)` where `x` is in
the source of `e`.
-/
@[expose]
def srcStar (Dₕ : Dihypergraph α) (x : α) : Set (Set α) := {s | ∃ e ∈ E(Dₕ), s = e.1 ∧ x ∈ s}

/--
The *destination star* of a vertex `x` is the set of all destinations of edges `e ∈ E(Dₕ)` where `x`
is in the destination of `e`.
-/
@[expose]
def dstStar (Dₕ : Dihypergraph α) (x : α) : Set (Set α) := {d | ∃ e ∈ E(Dₕ), d = e.2 ∧ x ∈ d}

/--
The *negative star* of a vertex `x` is the set of all edges `e ∈ E(Dₕ)` where `x` is in the source
of `e`.
-/
@[expose]
def negStar (Dₕ : Dihypergraph α) (x : α) : Set (Set α × Set α) := {e | e ∈ E(Dₕ) ∧ x ∈ e.1}

/--
The *negative degree* of a vertex `x` is the cardinality of the negative star of `x`.
-/
@[expose]
noncomputable def negDegree (Dₕ : Dihypergraph α) (x : α) : ℕ∞ := (Dₕ.negStar x).encard

/--
The *positive star* of a vertex `x` is the set of all edges `e ∈ E(Dₕ)` where `x` is in the
destination of `e`.
-/
@[expose]
def posStar (Dₕ : Dihypergraph α) (x : α) : Set (Set α × Set α) := {e | e ∈ E(Dₕ) ∧ x ∈ e.2}

/--
The *positive degree* of a vertex `x` is the cardinality of the positive star of `x`.
-/
@[expose]
noncomputable def posDegree (Dₕ : Dihypergraph α) (x : α) : ℕ∞ := (Dₕ.posStar x).encard

/-! Adjacency -/

/--
Edges `e` and `f` are adjacent if there is some vertex `x ∈ V(H)` where `x` is in the head of `e`
and in the tail of `f`.
-/
@[expose]
def EAdj (Dₕ : Dihypergraph α) (e : (Set α × Set α)) (f : (Set α × Set α)) : Prop :=
  e ∈ E(Dₕ) ∧ f ∈ E(Dₕ) ∧ ∃ x, x ∈ e.2 ∧ x ∈ f.1

lemma EAdj.exists_vertex (h : Dₕ.EAdj e f) : ∃ x ∈ V(Dₕ), x ∈ e.2 ∧ x ∈ f.1 := by
  grind only [eq_def, mem_vertexSet_of_mem_edgeSet_src_dst]

lemma EAdj.inter_nonempty (hef : Dₕ.EAdj e f) : (e.2 ∩ f.1).Nonempty := by
  grind only [eq_def, Set.inter_nonempty]

/-! ## Isolated vertices -/

/--
Predicate to determine if a vertex is isolated, meaning that it is not incident to any edges.
-/
@[expose]
def IsIsolated (Dₕ : Dihypergraph α) (x : α) : Prop := ∀ e ∈ E(Dₕ), x ∉ e.1 ∧ x ∉ e.2

@[simp]
lemma isIsolated_srcStar_empty (h : Dₕ.IsIsolated x) : Dₕ.srcStar x = ∅ := by
  grind [IsIsolated, srcStar]

lemma isIsolated_dstStar_empty (h : Dₕ.IsIsolated x) : Dₕ.dstStar x = ∅ := by
  grind [IsIsolated, dstStar]

@[simp]
lemma isIsolated_negStar_empty (h : Dₕ.IsIsolated x) : Dₕ.negStar x = ∅ := by
  grind [IsIsolated, negStar]

@[simp]
lemma isIsolated_negDegree_zero (h : Dₕ.IsIsolated x) : Dₕ.negDegree x = 0 := by
  grind [negDegree, Set.encard_eq_zero, isIsolated_negStar_empty]

@[simp]
lemma isIsolated_posStar_empty (h : Dₕ.IsIsolated x) : Dₕ.posStar x = ∅ := by
  grind [IsIsolated, posStar]

@[simp]
lemma isIsolated_posDegree_zero (h : Dₕ.IsIsolated x) : Dₕ.posDegree x = 0 := by
  grind [posDegree, Set.encard_eq_zero, isIsolated_posStar_empty]

/-! ## Empty Dihypergraphs -/

/--
Predicate to determine if a dihypergraph is nonempty
-/
@[expose]
def IsNonempty (Dₕ : Dihypergraph α) : Prop := V(Dₕ).Nonempty ∨ E(Dₕ).Nonempty

/-- The empty hypergraph (bottom) on a type. -/
@[simps]
instance (α : Type*) : Bot (Dihypergraph α) where
  bot.vertexSet := ∅
  bot.edgeSet := ∅
  bot.subset_vertexSet_of_src_dst_of_mem_edgeSet' := by simp

@[simp]
lemma IsNonempty.of_nonempty_vertexSet (hV : V(Dₕ).Nonempty) : Dₕ.IsNonempty :=
  .inl hV

@[simp]
lemma IsNonempty.of_nonempty_edgeSet (hE : E(Dₕ).Nonempty) : Dₕ.IsNonempty :=
  .inr hE

@[simp]
theorem ne_bot_iff : Dₕ ≠ ⊥ ↔ Dₕ.IsNonempty := by
  simp [IsNonempty, Set.nonempty_iff_ne_empty, Dihypergraph.ext_iff]
  grind [bot_vertexSet, bot_edgeSet]

alias ⟨_, IsNonempty.ne_bot⟩ := ne_bot_iff

@[simp]
theorem not_isNonempty_iff : ¬Dₕ.IsNonempty ↔ Dₕ = ⊥ :=
  not_iff_comm.mp ne_bot_iff

variable (Dₕ) in
lemma eq_bot_or_isNonempty : Dₕ = ⊥ ∨ Dₕ.IsNonempty := by
  have h : (V(Dₕ) = ∅ ∧ E(Dₕ) = ∅) ∨ (V(Dₕ).Nonempty ∨ E(Dₕ).Nonempty) := by grind [Set.Nonempty]
  cases h with
  | inl empty => (
    left
    apply Dihypergraph.ext empty.1 empty.2
  )
  | inr nonempty => (
    right
    grind [IsNonempty]
  )

lemma edge_not_mem_empty : e ∉ E(⊥) := by simp

/-! ## Trivial Dihypergraphs -/

/-- A dihypergraph is trivial if it has at least one vertex but no edges. -/
@[expose]
def IsTrivial (Dₕ : Dihypergraph α) : Prop := Set.Nonempty V(Dₕ) ∧ E(Dₕ) = ∅

/-- The trivial hypergraph with a given vertex set is defined by having no edges on that vertex
set. -/
@[simps, expose]
def trivialOn (s : Set α) : Dihypergraph α where
  vertexSet := s
  edgeSet := ∅
  subset_vertexSet_of_src_dst_of_mem_edgeSet' := by simp

lemma IsTrivial.trivialOn (hf : Set.Nonempty s) :
    IsTrivial (trivialOn s) := by
  grind [trivialOn, IsTrivial]

lemma IsTrivial.isNonempty (h : IsTrivial Dₕ) : IsNonempty Dₕ := by
  grind [IsNonempty, IsTrivial, Set.nonempty_iff_ne_empty]

lemma IsTrivial.not_mem_edgeSet (h : Dₕ.IsTrivial) : e ∉ E(Dₕ) := by grind [IsTrivial]

end Dihypergraph
