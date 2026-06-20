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

This module defines `DiHypergraph α` for a vertex type `α`. We represent an edge `e`
as a pair of sets of vertices (i.e., `e : (Set α) × (Set α)`). Each of the two sets in a directed
edge is called a *side* or a *limb*. The first side is called the *source* or the *tail*, and
the second side is called the *destination* or *head* of the edge.

## Main definitions

* `DiHypergraph α` is the type of dihypergraphs with vertices of type `α` and edges of type
  `(Set α × Set α)`. In addition to vertices and edges, a `DiHypergraph` must have the property
  that the sources and the destinations of all its edges are subsets of the vertex set.

For `Dₕ : DiHypergraph α`:

* `Dₕ.vertexSet` (abbrev. `V(Dₕ)`) denotes the vertex set of `Dₕ` as a term in `Set α`.
* `Dₕ.edgeSet` (abbrev. `E(Dₕ)`) denotes the edge set of `Dₕ` as a term in `((Set α) × (Set α))`.
* `Dₕ.IsBHypergraph`: A predicate defining a special case of dihypergraph where the destination of
  any edge (*B-arc*) contains exactly one vertex.
* `IsFHypergraph`: A predicate defining a special case of dihypergraph where the source of any edge
  (*F-arc*) contains exactly one vertex.
* `IsBFHypergraph`: A predicate defining a special case of dihypergraph where all edges are either
  B-arcs or F-arcs; i.e., either the source contains exactly one vertex or the destination
  contains exactly one vertex.
* `IsNonEndless`: A predicate defining a special case of dihypergraph where, for all edges, neither
  the source nor the destination are empty.

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
structure DiHypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The edge set -/
  edgeSet : Set ((Set α) × (Set α))
  /-- Each edge is a pair (s, d), where s ⊆ vertexSet and d ⊆ vertexSet -/
  subset_vertexSet_of_src_dst_of_mem_edgeSet' : (
    ∀ ⦃e⦄, e ∈ edgeSet → e.1 ⊆ vertexSet ∧ e.2 ⊆ vertexSet
  )

namespace DiHypergraph

variable {Dₕ Dₕ' : DiHypergraph α}

/-! ## Notation -/

/-- `V(Dₕ)` denotes the `vertexSet` of a dihypergraph `Dₕ` -/
scoped notation "V(" Dₕ ")" => DiHypergraph.vertexSet Dₕ

/-- `E(Dₕ)` denotes the `edgeSet` of a hypergraph `Dₕ` -/
scoped notation "E(" Dₕ ")" => DiHypergraph.edgeSet Dₕ

/-- TODO
lemma sUnion_edgeSet_subset_vertexSet : ⋃₀ E(H) ⊆ V(H) :=
  subset_powerset_iff.mp edgeSet_subset_powerset_vertexSet
-/

/-! ## DiHypergraph Basics -/

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

lemma mem_vertexSet_of_mem_src_edgeSet (he : e ∈ E(Dₕ)) (hx : x ∈ e.1) : x ∈ V(Dₕ) :=
  Dₕ.src_isSubset_vertexSet he hx

lemma mem_vertexSet_of_mem_dst_edgeSet (he : e ∈ E(Dₕ)) (hx : x ∈ e.2) : x ∈ V(Dₕ) :=
  Dₕ.dst_isSubset_vertexSet he hx

lemma edgeSet.ext_iff (he : e ∈ E(Dₕ)) (hf : f ∈ E(Dₕ)) :
    e = f ↔ ∀ x ∈ V(Dₕ), (x ∈ e.1 ↔ x ∈ f.1) ∧ (x ∈ e.2 ↔ x ∈ f.2) := by
  constructor
  · intro heq
    simp only [and_self, implies_true, heq]
  · intro hx
    grind only [Prod.ext_iff, mem_vertexSet_of_mem_src_edgeSet, mem_vertexSet_of_mem_dst_edgeSet]
    
lemma edgeSet_subset_powerset_vertexSet_vertexSet {Dₕ : DiHypergraph α} :
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
  mem_vertexSet_of_mem_edgeSet_src_dst he (by left; exact hx)

lemma mem_vertexSet_of_mem_edgeSet_dst (he : e ∈ E(Dₕ)) (hx : x ∈ e.2) : x ∈ V(Dₕ) :=
  mem_vertexSet_of_mem_edgeSet_src_dst he (by right; exact hx)

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
The *tail star* of a vertex `x` is the set of all tails of edges `e ∈ E(Dₕ)` where `x` is in the
tail of `e`.
-/
def tail_star (Dₕ : DiHypergraph α) (x : α) : Set (Set α) := {t | ∃ e ∈ E(Dₕ), t = e.1 ∧ x ∈ t}

/--
The *head star* of a vertex `x` is the set of all heads of edges `e ∈ E(Dₕ)` where `x` is in the
head of `e`.
-/
def head_star (Dₕ : DiHypergraph α) (x : α) : Set (Set α) := {h | ∃ e ∈ E(Dₕ), h = e.2 ∧ x ∈ e.2}

/--
The *negative star* of a vertex `x` is the set of all edges `e ∈ E(Dₕ)` where `x` is in the tail of
`e`.
-/
def negative_star (Dₕ : DiHypergraph α) (x : α) : Set (Set α × Set α) := {e | e ∈ E(Dₕ) ∧ x ∈ e.1}

/--
The *negative degree* of a vertex `x` is the cardinality of the negative star of `x`.
-/
noncomputable def negative_degree (Dₕ : DiHypergraph α) (x : α) : ℕ∞ := (Dₕ.negative_star x).encard

/--
The *positive star* of a vertex `x` is the set of all edges `e ∈ E(Dₕ)` where `x` is in the head of
`e`.
-/
def positive_star (Dₕ : DiHypergraph α) (x : α) : Set (Set α × Set α) := {e | e ∈ E(Dₕ) ∧ x ∈ e.2}

/--
The *positive degree* of a vertex `x` is the cardinality of the positive star of `x`.
-/
noncomputable def positive_degree (Dₕ : DiHypergraph α) (x : α) : ℕ∞ := (Dₕ.positive_star x).encard


/-! ## Special Cases -/
section SpecialCase

/--
A special case of `DiHypergraph` where all hyperedge destinations contain exactly one vertex.
-/
def IsBHypergraph (Dₕ : DiHypergraph α) := ∀ e ∈ E(Dₕ), ∃ x ∈ V(Dₕ), e.2 = {x}

/--
A special case of `DiHypergraph` where all hyperedge sources contain exactly one vertex.
-/
def IsFHypergraph (Dₕ : DiHypergraph α) :=  ∀ e ∈ E(Dₕ), ∃ x ∈ V(Dₕ), e.1 = {x}

/--
A special case of `DiHypergraph` where all hyperedges have a source containing exactly one vertex
or have a destination containing exactly one vertex.
-/
def IsBFHypergraph (Dₕ : DiHypergraph α) :=
  ∀ e ∈ E(Dₕ), (∃ x ∈ V(Dₕ), e.1 = {x}) ∨ (∃ x ∈ V(Dₕ), e.2 = {x})

/--
Many results related to directed hypergraphs assume that hyperedge sides are nonempty. We define
a hypergraph with nonempty hyperedge sources/destinations as a special case of dihypergraph, which
we call "non-endless".
-/
def IsNonEndless (Dₕ : DiHypergraph α) := ∀ e ∈ E(Dₕ), e.1.Nonempty ∧ e.2.Nonempty

end SpecialCase

/-! Adjacency -/

section Adjacency

/--
Two vertices `x` and `y` are adjacent if there is some edge `e ∈ E(H)` where `x` is in the tail of
`e`  and `y` is in the head of `e`.

Note that we do not need to explicitly check that x, y ∈ V(H) here because a vertex that is not in
the vertex set cannot be incident to any edge.
-/
def Adj (Dₕ : DiHypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(Dₕ), x ∈ e.1 ∧ y ∈ e.2

/--
Edges `e` and `f` are adjacent if there is some vertex `x ∈ V(H)` where `x` is in the head of `e`
and in the tail of `f`.
-/
def EAdj (Dₕ : DiHypergraph α) (e : (Set α × Set α)) (f : (Set α × Set α)) : Prop :=
  e ∈ E(Dₕ) ∧ f ∈ E(Dₕ) ∧ ∃ x, x ∈ e.2 ∧ x ∈ f.1

lemma EAdj.exists_vertex (h : Dₕ.EAdj e f) : ∃ x ∈ V(Dₕ), x ∈ e.2 ∧ x ∈ f.1 := by
  unfold EAdj at h
  obtain ⟨x, hx⟩ := h.2.2
  use x
  constructor
  · exact mem_vertexSet_of_mem_edgeSet_dst h.1 hx.1
  · exact hx

lemma EAdj.inter_nonempty (hef : Dₕ.EAdj e f) : (e.2 ∩ f.1).Nonempty := by
  unfold EAdj at *
  have h' : ∃ x ∈ e.2, x ∈ f.1 := by grind
  apply Set.inter_nonempty.mpr h'

end Adjacency

/-! ## Isolated vertices -/

section Isolated

/--
Predicate to determine if a vertex is isolated, meaning that it is not incident to any edges.
-/
def IsIsolated (Dₕ : DiHypergraph α) (x : α) : Prop := ∀ e ∈ E(Dₕ), x ∉ e.1 ∧ x ∉ e.2

@[simp]
lemma isIsolated_tailStar_empty (h : Dₕ.IsIsolated x) : Dₕ.tail_star x = ∅ := by
  unfold tail_star
  unfold IsIsolated at h
  apply Set.eq_empty_of_forall_notMem
  simp only [
    Prod.exists, exists_and_right, existsAndEq, true_and, mem_setOf_eq, not_and, forall_exists_index
  ]
  grind

lemma isIsolated_tailStar_isEmpty (h : Dₕ.IsIsolated x) : IsEmpty (Dₕ.tail_star x) := by
  rw [isIsolated_tailStar_empty h]
  apply Set.instIsEmptyElemEmptyCollection

lemma isIsolated_headStar_empty (h : Dₕ.IsIsolated x) : Dₕ.head_star x = ∅ := by
  unfold head_star
  unfold IsIsolated at h
  apply Set.eq_empty_of_forall_notMem
  simp only [
    Prod.exists, exists_and_right, existsAndEq, true_and, mem_setOf_eq, not_and, forall_exists_index
  ]
  grind

lemma isIsolated_headStar_isEmpty (h : Dₕ.IsIsolated x) : IsEmpty (Dₕ.head_star x) := by
  rw [isIsolated_headStar_empty h]
  apply Set.instIsEmptyElemEmptyCollection

@[simp]
lemma isIsolated_negativeStar_empty (h : Dₕ.IsIsolated x) : Dₕ.negative_star x = ∅ := by
  unfold negative_star
  unfold IsIsolated at h
  apply Set.eq_empty_of_forall_notMem
  simp only [mem_setOf_eq, not_and]
  grind

lemma isIsolated_negativeStar_isEmpty (h : Dₕ.IsIsolated x) : IsEmpty (Dₕ.negative_star x) := by
  rw [isIsolated_negativeStar_empty h]
  apply Set.instIsEmptyElemEmptyCollection

@[simp]
lemma isIsolated_negativeDegree_zero (h : Dₕ.IsIsolated x) : Dₕ.negative_degree x = 0 := by
  unfold negative_degree
  rw [isIsolated_negativeStar_empty h]
  apply Set.encard_eq_zero.mpr
  grind

@[simp]
lemma isIsolated_positiveStar_empty (h : Dₕ.IsIsolated x) : Dₕ.positive_star x = ∅ := by
  unfold positive_star
  unfold IsIsolated at h
  apply Set.eq_empty_of_forall_notMem
  simp only [mem_setOf_eq, not_and]
  grind

lemma isIsolated_positiveStar_isEmpty (h : Dₕ.IsIsolated x) : IsEmpty (Dₕ.positive_star x) := by
  rw [isIsolated_positiveStar_empty h]
  apply Set.instIsEmptyElemEmptyCollection

@[simp]
lemma isIsolated_positiveDegree_zero (h : Dₕ.IsIsolated x) : Dₕ.positive_degree x = 0 := by
  unfold positive_degree
  rw [isIsolated_positiveStar_empty h]
  apply Set.encard_eq_zero.mpr
  grind

end Isolated

/-! ## Empty Dihypergraphs -/

section Empty

/--
Predicate to determine if a dihypergraph is empty
-/
def IsEmpty (Dₕ : DiHypergraph α) : Prop := V(Dₕ) = ∅ ∧ E(Dₕ) = ∅

/--
Predicate to determine if a dihypergraph is nonempty
-/
def IsNonempty (Dₕ : DiHypergraph α) : Prop := (∃ x, x ∈ V(Dₕ)) ∨ (∃ e, e ∈ E(Dₕ))

@[simp]
lemma coe_nonempty : V(Dₕ).Nonempty → Dₕ.IsNonempty := by
  unfold IsNonempty
  unfold Set.Nonempty
  exact fun a ↦ Or.symm (Or.inr a)

/--
The empty dihypergraph of type α
-/
@[simps]
def emptyDiHypergraph (α : Type*) : DiHypergraph α where
  vertexSet := ∅
  edgeSet := ∅
  subset_vertexSet_of_src_dst_of_mem_edgeSet' := by
    intro e he
    exact False.elim he

lemma isEmpty_empty_hypergraph : IsEmpty (emptyDiHypergraph α) := by
  unfold IsEmpty
  exact Prod.mk_inj.mp rfl

lemma isEmpty_eq_empty_hypergraph (h : Dₕ.IsEmpty) : emptyDiHypergraph α = Dₕ := by
  unfold IsEmpty at h
  have hv : V(emptyDiHypergraph α) = ∅ := rfl
  have he : E(emptyDiHypergraph α) = ∅ := rfl
  apply DiHypergraph.ext_iff.mpr
  grind

lemma isBHypergraph_emptyDiHypergraph : (emptyDiHypergraph α).IsBHypergraph := by
  unfold IsBHypergraph
  simp

lemma isFHypergraph_emptyDiHypergraph : (emptyDiHypergraph α).IsFHypergraph := by
  unfold IsFHypergraph
  simp

lemma isBFHypergraph_emptyDiHypergraph : (emptyDiHypergraph α).IsBFHypergraph := by
  unfold IsBFHypergraph
  simp

lemma isNonEndless_emptyDiHypergraph : (emptyDiHypergraph α).IsNonEndless := by
  unfold IsNonEndless
  simp

lemma edge_not_mem_empty : e ∉ E(emptyDiHypergraph α) := by simp

lemma IsEmpty.eq (hDₕ : Dₕ.IsEmpty) : V(Dₕ) = ∅ ∧ E(Dₕ) = ∅ := hDₕ

@[simp]
lemma isEmpty_iff_forall_not_mem : Dₕ.IsEmpty ↔ (∀ x, x ∉ V(Dₕ)) ∧ (∀ e, e ∉ E(Dₕ)) := by
  grind [IsEmpty, Set.notMem_empty]

lemma IsEmpty.not_mem_vertex (hH : Dₕ.IsEmpty) : x ∉ V(Dₕ) := by
  unfold IsEmpty at hH
  grind

lemma IsEmpty.not_mem_edge (hH : Dₕ.IsEmpty) : e ∉ E(Dₕ) := by
  unfold IsEmpty at hH
  grind

lemma not_isEmpty : ¬Dₕ.IsEmpty ↔ Dₕ.IsNonempty := by grind [IsEmpty, IsNonempty]

lemma not_isNonempty : ¬Dₕ.IsNonempty ↔ Dₕ.IsEmpty := not_iff_comm.mp not_isEmpty

alias ⟨_, IsEmpty.not_isNonempty⟩ := not_isNonempty
alias ⟨_, IsNonempty.not_isEmpty⟩ := not_isEmpty

lemma isEmpty_or_isNonempty : Dₕ.IsEmpty ∨ Dₕ.IsNonempty := by grind [IsEmpty, IsNonempty]

end Empty

end DiHypergraph
