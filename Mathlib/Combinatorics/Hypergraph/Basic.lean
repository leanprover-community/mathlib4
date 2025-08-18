/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.Graph.Basic

open Set

variable {α β γ : Type*} {x y : α} {e f g h : Set α} {l : Set (Set α)}

/-!
# Undirected hypergraphs

An *undirected hypergraph* (here abbreviated as *hypergraph*) `H` is a generalization of a graph
(see `Mathlib.Combinatorics.Graph` or `Mathlib.Combinatorics.SimpleGraph`) and consists of a set of
*vertices*, usually denoted `V` or `V(H)`, and a set of *hyperedges*, denoted `E` or `E(H)`. In
contrast with a graph, where edges are unordered pairs of vertices, in hypergraphs, hyperedges are
(unordered) sets of vertices of length `0 ≤ |e| ≤ |V|`, where `e` is some hyperedge.

A hypergraph where `V = ∅` and `E = ∅` is *empty*. A hypergraph with a nonempty
vertex set (`V ≠ ∅`) and empty hyperedge set is *trivial*. A *complete hypergraph* is
one where `E(H) = 𝒫 V(H)`, where `𝒫 V(H)` is the *power set* of the vertex set.

If a hyperedge `e` contains only one vertex (i.e., `|e| = 1`), then it is a *loop*.

This module defines `Hypergraph α` for a vertex type `α` (hyperedges are defined as `Set Set α`).
In the near term, the hope is to provide an API for incidence and adjacency, as well as for
conversions:
- `Graph α β → Hypergraph α` (coersion/generalization of graph as 2-uniform hypergraph)
- `Hypergraph α → Graph α (α × α)` (as a *clique graph* or *two-section graph*)
- `Hypergraph α → Matrix α (Set α) γ` (the *incidence matrix* of the hypergraph)
- `Hypergraph α → Hypergraph α` (e.g., constructing the *dual* of a hypergraph)

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

From `Mathlib.Combinatorics.Graph.Basic`:
"The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation."

## Acknowledgments

Credit to Shreyas Srinivas, GitHub user @NotWearingPants ("Snir" on the Lean Zulip), Ammar
Husain, Aaron Liu, and Tristan Figueroa-Reid for patient guidance and useful feedback on this
implementation.
-/

structure Hypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The hyperedge set -/
  hyperedgeSet : Set (Set α)
  /-- All hyperedges must be subsets of the vertex set -/
  hyperedge_isSubset_vertexSet : ∀ ⦃e⦄, e ∈ hyperedgeSet → e ⊆ vertexSet

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `hyperedgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.hyperedgeSet H


section Incidence

/-! ## Vertex-Hyperedge Incidence -/

lemma vertex_mem_if_mem_hyperedge {H : Hypergraph α} (h : ∃ e ∈ H.hyperedgeSet, x ∈ e) :
x ∈ H.vertexSet := by
  obtain ⟨e, he⟩ := h
  have h1 : e ⊆ V(H) := by apply H.hyperedge_isSubset_vertexSet he.1
  apply Set.mem_of_subset_of_mem h1 he.2

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

lemma eAdj_imp_inter_nonempty {H : Hypergraph α} {e f : Set α} (hef : H.EAdj e f) :
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

section Extensionality

/-! ## Extensionality -/

-- TODO: this
-- Start here? https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/#propositional-extensionality

lemma ext {H₁ H₂ : Hypergraph α} (hv : V(H₁) = V(H₂)) (he : E(H₁) = E(H₂)) : H₁ = H₂ := by sorry

end Extensionality

section DefsPreds

/-! ## Basic Hypergraph Definitions & Predicates-/

/--
The set of all hyperedges `e ∈ E(H)` that a given vertex `x` is incident on
-/
def hyperedgesIncVertex (H : Hypergraph α) (x : α) : Set (Set α) := {e ∈ E(H) | x ∈ e }

/--
We define the *vertex hyperedge set* as the set of subsets of `E(H)` that each vertex in `V(H)` is
incident upon
-/
def hyperedgesIncVertices (H : Hypergraph α) : Set (Set (Set α)) :=
  {H.hyperedgesIncVertex x | x ∈ V(H)}

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
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := e ∈ E(H) ∧ Set.encard e = 1

/--
Predicate to determine if a hypergraph is empty
-/
def IsEmpty (H : Hypergraph α) : Prop := V(H) = ∅ ∧ E(H) = ∅

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

lemma isEmpty_empty_hypergraph {α : Type*} : IsEmpty (Hypergraph.emptyHypergraph α) := by
  unfold IsEmpty
  exact Prod.mk_inj.mp rfl

-- lemma isEmpty_eq_empty_hypergraph {H : Hypergraph α} (hh : IsEmpty H) : H = Hypergraph.emptyHypergraph α := by
--   have h0 : V(H) = ∅ ∧ E(H) = ∅ := by exact hh

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

/--
Predicate to determine is a hypergraph `H` is complete, meaning that each member of the power set of
the vertices (`𝒫 V(H)`) is represented in `E(H)`
-/
def IsComplete (H : Hypergraph α) : Prop := ∀ e ∈ 𝒫 V(H), e ∈ E(H)

/--
Predicate to determine if a hypergraph is simple

A simple hypergraph is one in which, for each hyperedge `e ∈ E(H)` (with associated vertex subset
`s : Set α`), there is no other hyperedge `f ∈ E(H)` (with associated vertex subset `t : Set α`)
such that `s ⊂ t`.
-/
def IsSimple (H : Hypergraph α) : Prop := ∀ e ∈ E(H), ∀ f ∈ E(H) \ {e}, ¬e ⊆ f

/--
Predicate to determine if a hypergraph is *`k`-uniform*.

In a `k`-uniform hypergraph `H`, all hyperedges `e ∈ E(H)` have the same cardinality, i.e.,
`|e| = k`.
-/
def IsKUniform (H : Hypergraph α) (k : ℕ) : Prop := ∀ e ∈ E(H), Set.ncard e = k

/--
Predicate to determine if a hypergraph is *`d`-regular*.

In a `d`-regular hypergraph `H`, all vertices `v ∈ V(H)` have the same degree, i.e., all vertices
are incident on `d` hyperedges.
-/
def IsDRegular (H : Hypergraph α) (d : ℕ) : Prop := ∀ l ∈ H.hyperedgesIncVertices, Set.ncard l = d

end DefsPreds

section Card

/-! ## Cardinality -/

/--
The *order* of a hypergraph `H` is defined as the number of vertices contained in `H`
-/
noncomputable def order (H : Hypergraph α) : ENat := Set.encard V(H)

/--
The *size* of a hypergraph `H` is defined as the number of hyperedges contained in `H`
-/
noncomputable def size (H : Hypergraph α) : ENat := Set.encard E(H)

/--
The set of vertex *degrees* of a hypergraph `H`.

A vertex `x` has degree `n`, where `n` is the number of hyperedges in `E(H)` that `x` is incident
on.
-/
noncomputable def vertexDegrees (H : Hypergraph α) : Set ENat :=
  {Set.encard l | l ∈ H.hyperedgesIncVertices}

/--
The set of hyperedge *degrees* of a hypergraph `H`.

A hyperedge `e` has degree `n`, where `n` is the number of vertices in `V(H)` that are incident on
`e`.
-/
noncomputable def hyperedgeDegrees (H : Hypergraph α) : Set ENat := {Set.encard e | e ∈ E(H)}

end Card

section Sub
/-! ## Subhypergraphs, Partial Hypergraphs, and Section Hypergraphs -/

/--
Given a subset of the vertex set `V(H)` of a hypergraph `H` (`g : Set α`), the
*subhypergraph* `Hg` has `V(Hg) = g ∩ V(H)`, and `E(Hg)` is the subset of `E(H)` for which all
incident vertices are included in `g`.
-/
def subHypergraph (H : Hypergraph α) (g : Set α) :=
  Hypergraph.mk
  (g ∩ V(H))
  {e | e ∈ E(H) ∧ e ⊆ g}
  (by
    intro f hf
    have h0 : f ∈ {e | e ∈ E(H) ∧ e ⊆ g} → f ∈ E(H) ∧ f ⊆ g := by apply Set.mem_sep_iff.mp
    have h1 : f ∈ E(H) ∧ f ⊆ g → f ⊆ V(H) ∧ f ⊆ g := by
      intro q
      have h1' : f ∈ E(H) := by exact q.left
      have h1'' : f ⊆ V(H) := by apply H.hyperedge_isSubset_vertexSet h1'
      constructor
      exact h1''
      exact q.right
    have h2 : f ⊆ V(H) ∧ f ⊆ g → f ⊆ V(H) ∩ g := by exact Set.subset_inter_iff.mpr
    apply h0 at hf
    apply h1 at hf
    apply h2 at hf
    rw [Set.inter_comm g V(H)]
    exact hf
  )

/--
Given a subset of the vertex set `V(H)` of a hypergraph `H` (`g`),the *induced subhypergraph* `Hg`
has `V(Hg) = g ∩ V(H)` and `E(Hg)` contains the subset of each hyperedge that intersects
with `g`.
-/
def inducedSubHypergraph (H : Hypergraph α) (g : Set α) :=
  Hypergraph.mk
  (g ∩ V(H))
  { { y | y ∈ (g ∩ e)} | e ∈ E(H) }
  (by
    intro q hq
    have h0 : ∃ e ∈ E(H), {y | y ∈ g ∩ e} = q := by exact hq
    obtain ⟨e, he⟩ := h0
    have h1 : e ⊆ V(H) := by exact H.hyperedge_isSubset_vertexSet he.left
    have h2 : q = {y | y ∈ g ∩ e} := by apply Eq.symm he.2
    have h3 : g ∩ e ⊆ g ∩ V(H) := by exact inter_subset_inter (fun ⦃a⦄ a ↦ a) h1
    exact Eq.trans_subset h2 h3
  )

/--
Given a subset of the hyperedge set `E(H)` of a hypergraph `H` (`l : Set (Set α)`), the
*partial hypergraph* `Hˡ` has `E(Hˡ) = l ∩ E(H)` and `V(Hˡ)` is the subset of `V(H)` which is
incident on at least one hyperedge in `E(Hˡ)`.
-/
def partialHypergraph (H : Hypergraph α) (l : Set (Set α)) : Hypergraph α where
  vertexSet := {x | ∃ e ∈ l, e ∈ E(H) ∧ x ∈ e}
  hyperedgeSet := l ∩ E(H)
  hyperedge_isSubset_vertexSet q hq _ hx := ⟨q, hq.1, hq.2, hx⟩

end Sub

section IncMatrix

/-! ## Incidence Matrix -/

/--
The *incidence matrix* `M` of a hypergraph `H` is a `|V(H)|`-by-`|E(H)|` matrix with elements:

`Mₓₑ = 1` if `x ∈ V(H) ∧ e ∈ E(H) ∧ x ∈ e`
`Mₓₑ = 0` otherwise

Note that this means that the incidence Matrix is defined even for members of α and Set α that are
not part of the hypergraph `H`.

TODO: there's no way this DecidableRel requirement is reasonable
-/
def incidenceMatrix (H : Hypergraph α)
[DecidableRel fun x e => x ∈ V(H) ∧ e ∈ E(H) ∧ x ∈ e] [Zero γ] [One γ] : Matrix α (Set α) γ :=
  Matrix.of (fun x e => ite (x ∈ V(H) ∧ e ∈ E(H) ∧ x ∈ e) 1 0)

end IncMatrix

end Hypergraph
