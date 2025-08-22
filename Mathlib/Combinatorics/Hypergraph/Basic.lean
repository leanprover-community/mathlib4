/-
Copyright (c) 2025 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith, Bhavik Mehta
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-!
# Undirected hypergraphs

An *undirected hypergraph* (here abbreviated as *hypergraph*) `H` is a generalization of a graph
(see `Mathlib.Combinatorics.Graph` or `Mathlib.Combinatorics.SimpleGraph`) and consists of a set of
*vertices*, usually denoted `V` or `V(H)`, and a set of *hyperedges*, denoted `E` or `E(H)`. In
contrast with a graph, where edges are unordered pairs of vertices, in hypergraphs, hyperedges are
(unordered) sets of vertices; i.e., they are subsets of the vertex set `V`.

A hypergraph where `V = ∅` and `E = ∅` is *empty*. A hypergraph with a nonempty
vertex set (`V ≠ ∅`) and empty hyperedge set is *trivial*.

If a hyperedge `e` contains only one vertex (i.e., `|e| = 1`), then it is a *loop*.

This module defines `Hypergraph α` for a vertex type `α` (hyperedges are defined as `Set (Set α)`).

## Main definitions

For `H : Hypergraph α`:

* `V(H)` denotes the vertex set of `H` as a term in `Set α`.
* `E(H)` denotes the hyperedge set of `H` as a term in `Set (Set α)`. Hyperedges must be subsets of
    `V(H)`.
* `H.Adj x y` means that there exists some hyperedge containing both `x` and `y` (or, in other
    words, `x` and `y` are incident on some shared hyperedge `e`).
* `H.EAdj e f` means that there exists some vertex that is incident on both hyperedge `e` and
    hyperedge `f : Set α`.

## Implementation details

This implementation is heavily inspired by Peter Nelson and Jun Kwon's `Graph` implementation,
which was in turn inspired by `Matroid`.

Paraphrasing `Mathlib.Combinatorics.Graph.Basic`:
"The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : Set α` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation."

Because `hyperedgeSet` is a `Set (Set α)`, rather than a multiset, here we are assuming that
all hypergraphs are *without repeated hyperedge*.

## Acknowledgments

Credit to Shreyas Srinivas, GitHub user @NotWearingPants ("Snir" on the Lean Zulip), Ammar
Husain, Aaron Liu, and Tristan Figueroa-Reid for patient guidance and useful feedback on this
implementation.
-/

open Set

variable {α β γ : Type*} {x y : α} {e e' f g : Set α} {l : Set (Set α)}

/--
An undirected hypergraph with vertices of type `α` and hyperedges of type `Set α`,
as described by vertex and hyperedge sets `vertexSet : Set α` and `hyperedgeSet : Set (Set α)`.

The requirement `hyperedge_isSubset_vertexSet` ensures that all vertices in hyperedges are part of
`vertexSet`, i.e., all hyperedges are subsets of the `vertexSet`.
-/
@[ext]
structure Hypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The hyperedge set -/
  hyperedgeSet : Set (Set α)
  /-- All hyperedges must be subsets of the vertex set -/
  hyperedge_isSubset_vertexSet' : ∀ ⦃e⦄, e ∈ hyperedgeSet → e ⊆ vertexSet

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `hyperedgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.hyperedgeSet H


instance : Membership (α) (Hypergraph α) where
  mem H x := x ∈ V(H)

instance : Membership (Set α) (Hypergraph α) where
  mem H e := e ∈ E(H)


section Incidence

/-! ## Vertex-Hyperedge Incidence -/

@[simp] lemma hyperedge_isSubset_vertexSet {H : Hypergraph α} {e : Set α} (he : e ∈ E(H)) :
  e ⊆ V(H) := H.hyperedge_isSubset_vertexSet' he

lemma _root_.Membership.mem.isSubset_vertexSet {H : Hypergraph α} {e : Set α} (he : e ∈ E(H)) :
  e ⊆ V(H) := H.hyperedge_isSubset_vertexSet he

lemma coe_isSubset_vertexSet_powerset {H : Hypergraph α} : E(H) ⊆ V(H).powerset := by
  intro e (he : e ∈ E(H))
  simpa using he.isSubset_vertexSet

lemma vertex_mem_if_mem_hyperedge {H : Hypergraph α} {e : Set α} {x : α}
  (he : e ∈ H.hyperedgeSet) (hx : x ∈ e) : x ∈ H.vertexSet := by
  have h1 : e ⊆ V(H) := by apply H.hyperedge_isSubset_vertexSet he
  apply Set.mem_of_subset_of_mem h1 hx

/--
If edges `e` and `e'` have the same vertices from `G`, then they have all the same vertices.
This could be phrased as `e = e'`, but this formulation is more useful in combination with the `ext`
tactic.
-/
lemma forall_of_forall_verts {e e' : Set α} (he : e ∈ E(H)) (he' : e' ∈ E(H))
    (h : ∀ x ∈ V(H), x ∈ e ↔ x ∈ e') : ∀ x, x ∈ e ↔ x ∈ e' :=
  fun x ↦ ⟨fun y ↦ (h x (he.isSubset_vertexSet y)).1 y,
  fun y ↦ (h x (he'.isSubset_vertexSet y)).2 y⟩

lemma sUnion_hyperedgeSet_subset_vertexSet : Set.sUnion E(H) ⊆ V(H) := by
  refine subset_powerset_iff.mp ?_
  exact coe_isSubset_vertexSet_powerset

end Incidence

section Adjacency

/-! ## Vertex and Hyperedge Adjacency -/

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some
hyperedge `e ∈ E(H)` where `x` and `y` are both incident on `e`.

Note that we do not need to explicitly check that x, y ∈ V(H) here because a vertex that is not in
the vertex set cannot be incident on any hyperedge.
-/
def Adj (H : Hypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(H), x ∈ e ∧ y ∈ e

lemma Adj.symm {H : Hypergraph α} {x y : α} (h : H.Adj x y) : H.Adj y x := by
  unfold Adj at *
  obtain ⟨e, he⟩ := h
  use e
  constructor
  · exact he.1
  constructor
  · exact he.2.2
  · exact he.2.1

-- Credit: Peter Nelson, Jun Kwon
lemma hypergraph_adj_comm (x y) : H.Adj x y ↔ H.Adj y x :=
  ⟨.symm, .symm⟩

/--
Predicate for (hyperedge) adjacency. Analogous to `Hypergraph.Adj`, hyperedges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident on both `e` and `f`.
-/
def EAdj (H : Hypergraph α) (e : Set α) (f : Set α) : Prop :=
  e ∈ E(H) ∧ f ∈ E(H) ∧ ∃ x ∈ V(H), x ∈ e ∧ x ∈ f

lemma EAdj.symm {H : Hypergraph α} {e f : Set α} (h : H.EAdj e f) : H.EAdj f e := by
  unfold EAdj at *
  obtain ⟨v, hv⟩ := h.2.2
  constructor
  · exact h.2.1
  constructor
  · exact h.1
  · use v
    constructor
    · exact hv.1
    constructor
    · exact hv.2.2
    · exact hv.2.1

lemma EAdj.inter_nonempty {H : Hypergraph α} {e f : Set α} (hef : H.EAdj e f) :
  (e ∩ f).Nonempty := by
    unfold EAdj at *
    have h' : ∃ x ∈ e, x ∈ f := by grind
    apply Set.inter_nonempty.mpr h'

-- Credit: Peter Nelson, Jun Kwon
lemma hypergraph_eadj_comm (e f) : H.EAdj e f ↔ H.EAdj f e :=
  ⟨.symm, .symm⟩

/--
Neighbors of a vertex `x` in hypergraph `H`

A vertex `y` is a neighbor of vertex `x` if there exists some hyperedge `e ∈ E(H)` where `x` and
`y` are both incident on `e`, i.e., if the two vertices are adjacent (see `Hypergraph.Adj`)
-/
def neighbors (H : Hypergraph α) (x : α) : Set α := {y | H.Adj x y}

/--
Neighbors of a hyperedge `e` in hypergraph `H`

A hyperedge `f` is a neighbor of hyperedge `e` if there exists some vertex `x ∈ V(H)` where `x` is
incident on both `e` and `f`, i.e., if the two hyperedges are adjacent (see `Hypergraph.EAdj`)
-/
def hyperedgeNeighbors (H : Hypergraph α) (e : Set α) : Set (Set α) := {f | H.EAdj e f}

end Adjacency

section DefsPreds

/-! ## Basic Hypergraph Definitions & Predicates-/

/--
The *star* of a vertex is the set of all hyperedges `e ∈ E(H)` that a given vertex `x` is incident
on
-/
def star (H : Hypergraph α) (x : α) : Set (Set α) := {e ∈ E(H) | x ∈ e}

/--
We define the *star set* as the set of subsets of `E(H)` that each vertex in `V(H)` is
incident upon
-/
def stars (H : Hypergraph α) : Set (Set (Set α)) :=
  {H.star x | x ∈ V(H)}

@[simps]
def image (H : Hypergraph α) (f : α → β) : Hypergraph β where
  vertexSet := V(H).image f
  hyperedgeSet := E(H).image (Set.image f)
  hyperedge_isSubset_vertexSet' := by
    simp
    intro e he
    have hev : e ⊆ V(H) := by exact Membership.mem.isSubset_vertexSet he
    refine image_subset_iff.mp ?_
    exact image_mono hev

@[simp] lemma mem_image {f : α → β} {e : Set β} {H : Hypergraph α} :
    e ∈ H.image f ↔ ∃ e' ∈ E(H), e'.image f = e := by exact Eq.to_iff rfl

lemma image_mem_image {f : α → β} {e : Set α} {H : Hypergraph α} (he : e ∈ E(H)) :
    e.image f ∈ E(H.image f) :=
  mem_image_of_mem _ he

lemma image_image
    {f : α → β} {g : β → γ} (H : Hypergraph α) :
    (H.image f).image g = H.image (g ∘ f) := by
  ext : 1
  case vertexSet => simp [Set.image_image]
  case hyperedgeSet => simp [Set.image_image]

/--
Predicate to determine if a vertex is isolated, meaning that it is not incident on any hyperedges.
Note that this includes loops, i.e., if vertex `x` is isolated, there is no hyperedge with
associated vertex subset `{x}`
-/
def IsIsolated (H : Hypergraph α) (x : α) : Prop := ∀ e ∈ E(H), x ∉ e

lemma not_exists_isolated_vertex_iff_sUnion_hyperedgeSet_eq_vertexSet {H : Hypergraph α} :
Set.sUnion E(H) = V(H) ↔ ∀ x ∈ V(H), ¬IsIsolated H x :=
  Iff.intro
  (by
    unfold IsIsolated
    intro h
    grind
  )
  (by
    unfold IsIsolated
    intro h
    have h' : ∀ x ∈ V(H), ∃ e ∈ E(H), x ∈ e := by grind
    refine Subset.antisymm ?_ h'
    apply Set.sUnion_subset
    exact fun t' a ↦ H.hyperedge_isSubset_vertexSet a
  )

/--
Predicate to determine if a hyperedge `e` is a loop, meaning that its associated vertex subset `s`
contains only one vertex, i.e., `|s| = 1`
-/
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := ∃ x ∈ V(H), e = {x}

lemma isLoop_encard_one {H : Hypergraph α} {e : Set α} (h : H.IsLoop e) : Set.encard e = 1 := by
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
def IsNonempty (H : Hypergraph α) : Prop := ∃ x, x ∈ V(H)

/--
The empty hypergraph of type α
-/
def emptyHypergraph (α : Type*) : Hypergraph α :=
  Hypergraph.mk
  ∅
  ∅
  (by
    intro e he
    have h1 : e = ∅ := by exact False.elim he
    exact Set.subset_empty_iff.mpr h1
  )

@[simp] lemma coe_nonempty_iff : V(H).Nonempty ↔ H.IsNonempty := Iff.rfl

lemma isEmpty_empty_hypergraph {α : Type*} : IsEmpty (Hypergraph.emptyHypergraph α) := by
  unfold IsEmpty
  exact Prod.mk_inj.mp rfl

@[simp]
lemma isEmpty_eq_empty_hypergraph {H : Hypergraph α} (h : H.IsEmpty) : H = emptyHypergraph α := by
  exact Hypergraph.ext_iff.mpr h

@[simp]
lemma hyperedge_not_mem_empty {α : Type*} {e : Set α} : e ∉ E(emptyHypergraph α) :=
  by exact fun a ↦ a

lemma IsEmpty.eq (hH : H.IsEmpty) : V(H) = ∅ ∧ E(H) = ∅ := by exact hH

lemma isEmpty_iff_forall_not_mem : H.IsEmpty ↔ (∀ x, x ∉ V(H)) ∧ (∀ e, e ∉ E(H)) := by
  unfold IsEmpty
  constructor
  · intro h
    constructor
    · rw [h.1]
      apply Set.notMem_empty
    · rw [h.2]
      apply Set.notMem_empty
  · intro ho
    constructor
    · apply Set.eq_empty_iff_forall_notMem.mpr
      apply ho.left
    · apply Set.eq_empty_iff_forall_notMem.mpr
      apply ho.right

lemma IsEmpty.not_mem (hH : H.IsEmpty) {e : Set α} : e ∉ E(H) := by
  unfold IsEmpty at hH
  rw [hH.2]
  exact fun a ↦ a

@[simp] lemma not_isEmpty : ¬ H.IsEmpty ↔ H.IsNonempty := by
  rw [IsEmpty, ← coe_nonempty_iff]
  constructor
  rw [not_and_or]
  intro h
  cases h with
  | inl v_nonempty => exact nonempty_iff_ne_empty.mpr v_nonempty
  | inr e_nonempty => by sorry

@[simp] lemma not_isNonempty : ¬ H.IsNonempty ↔ H.IsEmpty :=
  not_iff_comm.mp not_isEmpty

alias ⟨_, IsEmpty.not_isNonempty⟩ := not_isNonempty
alias ⟨_, IsNonempty.not_isEmpty⟩ := not_isEmpty

variable (G) in
lemma isEmpty_or_isNonempty : G.IsEmpty ∨ G.IsNonempty := G.edges.eq_empty_or_nonempty

@[simp] lemma empty_isEmpty (S : Finset α) : (empty S).IsEmpty := rfl

/-- A hypergraph is empty if and only if it is the empty hypergraph on some vertex set. -/
lemma isEmpty_iff_eq_empty : G.IsEmpty ↔ ∃ S, G = empty S := by
  refine ⟨fun h ↦ ⟨G.verts, ?_⟩, fun ⟨S, h⟩ ↦ h.symm ▸ empty_isEmpty S⟩
  ext : 1
  case verts => simp
  case edges => simp [h.eq]

@[simp] lemma completeOn_isNonempty {S : Finset α} : (completeOn S).IsNonempty :=
  powerset_nonempty _


/--
Predicate to determine if a hypergraph is trivial

A hypergraph is trivial if it has a nonempty vertex set and an empty hyperedge set
-/
def IsTrivial (H : Hypergraph α) : Prop := Set.Nonempty V(H) ∧ E(H) = ∅

/--
A trivial hypergraph of type α with vertex set h
-/
def trivialHypergraph {α : Type*} (h : Set α) :=
  Hypergraph.mk
  h
  ∅
  (by
    intro e he
    exact False.elim he
  )

lemma not_isEmpty_trivial_hypergraph {H : Hypergraph α} (hh : IsTrivial H) : ¬IsEmpty H := by
  unfold IsEmpty
  unfold IsTrivial at hh
  refine not_and_of_not_or_not ?_
  left
  apply Set.nonempty_iff_ne_empty.mp hh.1

@[simp]
lemma hyperedge_not_mem_trivial {α : Type*} {e : Set α} {H : Hypergraph α} (h : H.IsTrivial) :
  e ∉ E(H) := by
    unfold IsTrivial at *
    grind

/--
Predicate to determine is a hypergraph `H` is complete, meaning that each member of the power set of
the vertices (`𝒫 V(H)`) is represented in `E(H)`
-/
def IsComplete (H : Hypergraph α) : Prop := ∀ e ∈ 𝒫 V(H), e ∈ E(H)

@[simps]
def completeOn (f : Set α) : Hypergraph α where
  vertexSet := f
  hyperedgeSet := 𝒫 f
  hyperedge_isSubset_vertexSet' := by simp

@[simp]
lemma mem_completeOn {e f : Set α} : e ∈ E(completeOn f) ↔ e ⊆ f := by
  constructor
  · exact fun a ↦ a
  · exact fun a ↦ a

@[simp]
lemma isComplete_completeOn (f : Set α) : (completeOn f).IsComplete := by exact fun e a ↦ a

end DefsPreds

end Hypergraph
