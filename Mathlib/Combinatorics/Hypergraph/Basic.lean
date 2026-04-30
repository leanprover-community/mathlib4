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

## Acknowledgments

Credit to Shreyas Srinivas, GitHub user @NotWearingPants ("Snir" on the Lean Zulip), Ammar
Husain, Aaron Liu, Tristan Figueroa-Reid, and John Talbot for patient guidance and useful feedback
on this implementation.
-/

@[expose] public section

open Set

variable {α β γ : Type*} {x y : α} {e e' f g : Set α} {l : Set (Set α)}

/--
An undirected hypergraph with vertices of type `α` and edges of type `Set α`, as described by vertex
and edge sets `vertexSet : Set α` and `edgeSet : Set (Set α)`.

The requirement `edge_isSubset_vertexSet` ensures that all vertices in edges are part of
`vertexSet`, i.e., all edges are subsets of the `vertexSet`.
-/
@[ext]
structure Hypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The edge set -/
  edgeSet : Set (Set α)
  /-- All edges must be subsets of the vertex set -/
  edge_isSubset_vertexSet' : ∀ ⦃e⦄, e ∈ edgeSet → e ⊆ vertexSet

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `edgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.edgeSet H


/-! ## Vertex-Hyperedge Incidence -/

@[simp]
lemma edge_isSubset_vertexSet (he : e ∈ E(H)) : e ⊆ V(H) :=
  H.edge_isSubset_vertexSet' he

lemma _root_.Membership.mem.subset_vertexSet (he : e ∈ E(H)) : e ⊆ V(H) :=
  H.edge_isSubset_vertexSet he

lemma edgeSet_subset_powerset_vertexSet {H : Hypergraph α} : E(H) ⊆ V(H).powerset := by
  intro e (he : e ∈ E(H))
  simpa using he.subset_vertexSet

lemma mem_vertexSet_of_mem_edgeSet (he : e ∈ E(H)) (hx : x ∈ e) : x ∈ V(H) := by
  have h1 : e ⊆ V(H) := by apply H.edge_isSubset_vertexSet he
  apply Set.mem_of_subset_of_mem h1 hx

/--
If edges `e` and `e'` have the same vertices from `G`, then they have all the same vertices.
This could be phrased as `e = e'`, but this formulation is more useful in combination with the `ext`
tactic.
-/
lemma forall_of_forall_verts (he : e ∈ E(H)) (he' : e' ∈ E(H))
    (h : ∀ x ∈ V(H), x ∈ e ↔ x ∈ e') : ∀ x, x ∈ e ↔ x ∈ e' :=
  fun x ↦ ⟨fun y ↦ (h x (he.subset_vertexSet y)).1 y,
  fun y ↦ (h x (he'.subset_vertexSet y)).2 y⟩

lemma sUnion_edgeSet_subset_vertexSet : ⋃₀ E(H) ⊆ V(H) := by
  refine subset_powerset_iff.mp ?_
  exact edgeSet_subset_powerset_vertexSet

/-! ## Vertex and Hyperedge Adjacency -/

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some edge `e ∈ E(H)`
where `x` and `y` are both incident to `e`.

Note that we do not need to explicitly check that x, y ∈ V(H) here because a vertex that is not in
the vertex set cannot be incident to any edge.
-/
def Adj (H : Hypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(H), x ∈ e ∧ y ∈ e

lemma Adj.symm (h : H.Adj x y) : H.Adj y x := by grind [Adj]

-- Credit: Peter Nelson, Jun Kwon
lemma adj_comm (x y : α) : H.Adj x y ↔ H.Adj y x := ⟨.symm, .symm⟩

/--
Predicate for edge adjacency. Analogous to `Hypergraph.Adj`, edges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident to both `e` and `f`.
-/
def EAdj (H : Hypergraph α) (e : Set α) (f : Set α) : Prop :=
  e ∈ E(H) ∧ f ∈ E(H) ∧ ∃ x, x ∈ e ∧ x ∈ f

lemma EAdj.exists_vertex (h : H.EAdj e f) : ∃ x ∈ V(H), x ∈ e ∧ x ∈ f := by
  unfold EAdj at h
  obtain ⟨x, hx⟩ := h.2.2
  use x
  constructor
  · exact mem_vertexSet_of_mem_edgeSet h.1 hx.1
  · exact hx

lemma EAdj.symm (h : H.EAdj e f) : H.EAdj f e := by grind [EAdj]

lemma EAdj.inter_nonempty (hef : H.EAdj e f) : (e ∩ f).Nonempty := by
  unfold EAdj at *
  have h' : ∃ x ∈ e, x ∈ f := by grind
  apply Set.inter_nonempty.mpr h'

-- Credit: Peter Nelson, Jun Kwon
lemma eAdj_comm (e f) : H.EAdj e f ↔ H.EAdj f e := ⟨.symm, .symm⟩

/-! ## Basic Hypergraph Definitions & Predicates-/

/--
The *star* of a vertex is the set of all edges `e ∈ E(H)` that a given vertex `x` is incident to
-/
def star (H : Hypergraph α) (x : α) : Set (Set α) := {e ∈ E(H) | x ∈ e}

/--
We define the *star set* as the set of subsets of `E(H)` that each vertex in `V(H)` is
incident to
-/
def stars (H : Hypergraph α) : Set (Set (Set α)) := {H.star x | x ∈ V(H)}

/--
The *image* of a hypergraph `H : Hypergraph α` under function `f : α → β` is `Hᶠ : Hypergraph β`.

The vertex set of `Hᶠ` is the image of `V(H)` under `f`, and the edge set of `Hᶠ` is the set of
images of the edges (subsets of vertices) in `E(H)`.
-/
@[simps]
def image (H : Hypergraph α) (f : α → β) : Hypergraph β where
  vertexSet := V(H).image f
  edgeSet := E(H).image (Set.image f)
  edge_isSubset_vertexSet' := by
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, image_subset_iff]
    intro e he
    have hev : e ⊆ V(H) := by exact Membership.mem.subset_vertexSet he
    refine image_subset_iff.mp ?_
    exact image_mono hev

lemma mem_image {f : α → β} {e : Set β} : e ∈ E(H.image f) ↔ ∃ e' ∈ E(H), f '' e' = e := Iff.rfl

lemma image_mem_image {f : α → β} (he : e ∈ E(H)) : e.image f ∈ E(H.image f) :=
  mem_image_of_mem _ he

lemma image_image {f : α → β} {g : β → γ} (H : Hypergraph α) :
  (H.image f).image g = H.image (g ∘ f) := by
    ext : 1
    case vertexSet => simp [Set.image_image]
    case edgeSet => simp [Set.image_image]

/--
Predicate to determine if a vertex is isolated, meaning that it is not incident to any edges. Note
that this includes loops, i.e., if vertex `x` is isolated, there is no edge with associated vertex
subset `{x}`.
-/
def IsIsolated (H : Hypergraph α) (x : α) : Prop := ∀ e ∈ E(H), x ∉ e

lemma not_exists_isolated_vertex_iff_sUnion_edgeSet_eq_vertexSet :
  ⋃₀ E(H) = V(H) ↔ ∀ x ∈ V(H), ¬IsIsolated H x :=
    Iff.intro
    (by grind [IsIsolated])
    (by
      unfold IsIsolated
      intro h
      have h' : ∀ x ∈ V(H), ∃ e ∈ E(H), x ∈ e := by grind
      refine Subset.antisymm ?_ h'
      apply Set.sUnion_subset
      exact fun t' a ↦ H.edge_isSubset_vertexSet a
    )

/--
Predicate to determine if a edge `e` is a loop, meaning that its associated vertex subset `s`
contains only one vertex, i.e., `|s| = 1`
-/
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := ∃ x ∈ V(H), e = {x}

lemma isLoop_encard_one (h : H.IsLoop e) : Set.encard e = 1 := by
  unfold IsLoop at h
  refine encard_eq_one.mpr ?_
  obtain ⟨x, hx⟩ := h
  use x
  exact hx.2

/--
Predicate to determine if a hypergraph is empty
-/
def IsEmpty (H : Hypergraph α) : Prop := V(H) = ∅ ∧ E(H) = ∅

/--
Predicate to determine if a hypergraph is nonempty
-/
def IsNonempty (H : Hypergraph α) : Prop := (∃ x, x ∈ V(H)) ∨ (∃ e, e ∈ E(H))

/--
The empty hypergraph of type α
-/
@[simps]
def emptyHypergraph (α : Type*) : Hypergraph α where
  vertexSet := ∅
  edgeSet := ∅
  edge_isSubset_vertexSet' := by
    intro e he
    have h1 : e = ∅ := by exact False.elim he
    exact Set.subset_empty_iff.mpr h1

@[simp] lemma coe_nonempty : V(H).Nonempty → H.IsNonempty := by
  unfold IsNonempty
  unfold Set.Nonempty
  exact fun a ↦ Or.symm (Or.inr a)

lemma isEmpty_empty_hypergraph : IsEmpty (Hypergraph.emptyHypergraph α) := by
  unfold IsEmpty
  exact Prod.mk_inj.mp rfl

lemma isEmpty_eq_empty_hypergraph (h : H.IsEmpty) : emptyHypergraph α = H := by
  unfold IsEmpty at h
  have hv : V(emptyHypergraph α) = ∅ := rfl
  have he : E(emptyHypergraph α) = ∅ := rfl
  apply Hypergraph.ext_iff.mpr
  grind

lemma edge_not_mem_empty : e ∉ E(emptyHypergraph α) := by simp

lemma IsEmpty.eq (hH : H.IsEmpty) : V(H) = ∅ ∧ E(H) = ∅ := by exact hH

@[simp]
lemma isEmpty_iff_forall_not_mem : H.IsEmpty ↔ (∀ x, x ∉ V(H)) ∧ (∀ e, e ∉ E(H)) := by
  grind [IsEmpty, Set.notMem_empty]

lemma IsEmpty.not_mem (hH : H.IsEmpty) {e : Set α} : e ∉ E(H) := by
  unfold IsEmpty at hH
  grind

lemma not_isEmpty : ¬H.IsEmpty ↔ H.IsNonempty := by grind [IsEmpty, IsNonempty]

lemma not_isNonempty : ¬H.IsNonempty ↔ H.IsEmpty := not_iff_comm.mp not_isEmpty

alias ⟨_, IsEmpty.not_isNonempty⟩ := not_isNonempty
alias ⟨_, IsNonempty.not_isEmpty⟩ := not_isEmpty

variable (H) in
lemma isEmpty_or_isNonempty : H.IsEmpty ∨ H.IsNonempty := by grind [IsEmpty, IsNonempty]

/--
Predicate to determine if a hypergraph is trivial

A hypergraph is trivial if it has a nonempty vertex set and an empty edge set
-/
def IsTrivial (H : Hypergraph α) : Prop := Set.Nonempty V(H) ∧ E(H) = ∅

/--
A trivial hypergraph of type α with vertex set h
-/
@[simps]
def trivialHypergraph (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := ∅
  edge_isSubset_vertexSet' := by
    intro e he
    exact False.elim he

lemma not_isEmpty_trivial_hypergraph (hh : IsTrivial H) : ¬IsEmpty H := by
  grind [IsEmpty, IsTrivial, Set.nonempty_iff_ne_empty]

lemma edge_not_mem_trivial (h : H.IsTrivial) : e ∉ E(H) := by grind [IsTrivial]

/--
Predicate to determine is a hypergraph `H` is complete, meaning that each member of the power set of
the vertices (`𝒫 V(H)`) is represented in `E(H)`
-/
def IsComplete (H : Hypergraph α) : Prop := ∀ e ∈ 𝒫 V(H), e ∈ E(H)

/--
A complete hypergraph with vertex set f
-/
@[simps]
def completeOn (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := 𝒫 f
  edge_isSubset_vertexSet' := by simp

lemma mem_completeOn : e ∈ E(completeOn f) ↔ e ⊆ f := by simp

lemma isComplete_completeOn (f : Set α) : (completeOn f).IsComplete := by exact fun e a ↦ a

lemma isComplete_not_isEmpty (h : H.IsComplete) : ¬ H.IsEmpty := by
  unfold IsComplete at h
  unfold IsEmpty
  have h0 : ∅ ∈ 𝒫 V(H) := by
    refine mem_powerset ?_
    apply Set.empty_subset
  apply not_and_or.mpr
  right
  grind

lemma completeOn_isNonempty {S : Set α} : (completeOn S).IsNonempty := by
  have h : E(completeOn S) = 𝒫 S := rfl
  have h' : ∅ ∈ E(completeOn S) := by
    refine mem_completeOn.mpr ?_
    apply Set.empty_subset
  unfold IsNonempty
  right
  use ∅

lemma isComplete_not_isTrivial (h : H.IsComplete) : ¬H.IsTrivial := by
  unfold IsComplete at h
  unfold IsTrivial
  have h' : ∅ ∈ E(H) := by grind
  apply not_and_or.mpr
  right
  exact ne_of_mem_of_not_mem' h' fun a ↦ a

lemma completeOn_not_isTrivial {S : Set α} : ¬(completeOn S).IsTrivial := by
  unfold IsTrivial
  apply not_and_or.mpr
  right
  exact ne_of_mem_of_not_mem' (fun ⦃a⦄ a ↦ a) fun a ↦ a

end Hypergraph
