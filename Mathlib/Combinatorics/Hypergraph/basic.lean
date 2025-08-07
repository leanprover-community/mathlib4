/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2

variable {α β : Type*} {x y z : α} {s t : Set α} {e f g : β}

open Set

/-!

# Undirected hypergraphs

An *undirected hypergraph* (here abbreviated as *hypergraph*) `H` is a generalization of a graph
(see `Mathlib.Combinatorics.Graph`) and consists of a set of *vertices*, usually denoted `V` or
`V(H)`, and a set of *hyperedges*, denoted `E` or `E(H)`. In contrast with a graph, where edges are
unordered pairs of vertices, in hypergraphs, hyperedges are (unordered) sets of vertices of length
`0 ≤ |e| ≤ |V|`, where `e` is some hyperedge.

A hypergraph where `V = ∅` and `E = ∅` is called an *empty hypergraph*. A hypergraph with a nonempty
vertex set (`V ≠ ∅`) and empty hyperedge set is a *trivial hypergraph*. A *complete hypergraph* is
one where `E(H) = P(V)`, where `P(V)` is the *power set* of the vertex set. Note that one can only
have a complete hypergraph when the vertex set is finite.

If a hyperedge `e` contains only one vertex (i.e., `|e| = 1`), then it is a *loop*

This module defines `Hypergraph α β` for a vertex type `α` and a hyperedge type `β`.
In the near term, the hope is to provide an API for incidence and adjacency, as well as for
conversions:
- `Graph α β` ⇒ `Hypergraph α β` (coersion/generalization of graph)
- `Hypergraph α β` ⇒ `Graph α β` (as a *clique graph* or *two-section graph*)
- `Hypergraph α β` ⇒ `Matrix α β Bool` (the *incidence matrix* of the hypergraph)
- `Hypergraph α β` ⇒ `Hypergraph β α` (i.e., constructing the *dual* of a hypergraph)

Other (future) aspects of interest:
- Hyperpaths
- Random hypergraphs

## Main definitions

For `H : Hypergraph α β`, ...

* `V(H)` denotes the vertex set of `H` as a term in `Set α`.
* `E(H)` denotes the hyperedge set of `H` as a term in `Set β`.
* `H.IsIncident a x` means that the vertex `x : α` is a member of (or is *incident* on) the
    hyperedge `e : β`.
* `H.IsHyperedge e s` means that the hyperedge `x` contains exactly the vertices contained in
    `s : Set α`.
* `H.Adj x y` means that there exists some hyperedge containing both `x` and `y`.
* `H.EAdj e f` means that there exists some vertex that is incident on both hyperedge `e` and
    hyperedge `f : β`.

TODO:
  - Do we need IsLoop/IsNonLoop? (see `Mathlib.Combinatorics.Graph`)

## Implementation details

This implementation is heavily inspired by Peter Nelson and Jun Kwon's `Graph` implementation,
which was in turn inspired by `Matroid`.

From `Mathlib.Combinatorics.Graph.Basic`:
"The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation."
-/

structure Hypergraph (α β : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The hyperedge set. Currently representing this as a Set
    TODO: Multiset β would be more general... -/
  hyperedgeSet: Set β
  /-- Incidence predicate stating that a vertex `x` is a member of hyperedge `e` -/
  IsIncident : α → β → Prop


namespace Hypergraph

variable {H : Hypergraph α β}

/-! ## Notation-/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `hyperedgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.hyperedgeSet H

/--
The empty hypergraph

An empty hypergraph contains an empty vertex set and an empty hyperedge set
-/
def emptyHypergraph (α β : Type*) : Hypergraph α β := Hypergraph.mk ∅ ∅ (fun _ _ => False)

/--
Predicate to determine if a hypergraph is empty
-/
def IsEmpty (H : Hypergraph α β) : Prop := V(H) = ∅ ∧ E(H) = ∅

/--
Predicate to determine if a hypergraph is trivial

A hypergraph is trivial if it has a nonempty vertex set and an empty hyperedge set
-/
def IsTrivial (H : Hypergraph α β) : Prop := Nonempty V(H) ∧ E(H) = ∅

-- * `H.IsHyperedge e s` means that the hyperedge `x` contains exactly the vertices contained in
--     `s : Set α`.
-- * `H.Adj x y` means that there exists some hyperedge containing both `x` and `y`.
-- * `H.EAdj e f` means that there exists some vertex that is incident on both hyperedge `e` and
--     hyperedge `f : β`.

/--
Predicate to determine if a hyperedge `e` contains exactly the vertex subset `s : Set α`
-/
def IsHyperedge (H : Hypergraph α β) (e : β) (s : Set α) : Prop :=
  (∀ x ∈ s, x ∈ V(H) ∧ H.IsIncident x e) ∧ (∀ y ∈ V(H) \ s, ¬H.IsIncident y e)

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some
hyperedge `e ∈ E(H)` where `x` and `y` are both incident on `e`.

Note that we do not need to explicitly check that x, y ∈ V(H) here because a vertex that is not in
the vertex set cannot be incident on any hyperedge.
-/
def Adj (H : Hypergraph α β) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(H), H.IsIncident x e ∧ H.IsIncident y e

/--
Predicate for (hyperedge) adjacency. Analogous to `Hypergraph.Adj`, hyperedges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident on both `e` and `f`.

Note that we do not need to explicitly check that e, f ∈ E(H) here because a vertex cannot be
incident on a hyperedge that is not in the hyperedge set.
-/
def EAdj (H : Hypergraph α β) (e : β) (f : β) : Prop :=
  ∃ x ∈ V(H), H.IsIncident x e ∧ H.IsIncident x f

/--
Predicate to determine if a hyperedge `e` is a loop, meaning that its associated vertex subset `s`
contains only one vertex, i.e., `|s| = 1`

TODO: am I using Set.encard right?
-/
def IsLoop (H : Hypergraph α β) (e : β) (s : Set α) : Prop :=
  H.IsHyperedge e s ∧ (Set.encard s) = 1

/--
Predicate to determine if a hypergraph is simple

A simple hypergraph is one in which, for each hyperedge `e ∈ E(H)` (with associated vertex subset
`s : Set α`), there is no other hyperedge `f ∈ E(H)` (with associated vertex subset `t : Set α`)
such that `s ⊂ t`.

TODO: define this in a sane way
-/
def IsSimple (H : Hypergraph α β) : Prop := sorry



end Hypergraph
