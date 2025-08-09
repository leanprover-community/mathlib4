/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2

open Set

variable {α β : Type*} {x y z : α} {s t : Set α} {e f g : β} {l m : Set β}

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
- Finiteness
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
* `H.Adj x y` means that there exists some hyperedge containing both `x` and `y` (or, in other
    words, `x` and `y` are incident on some shared hyperedge `e`).
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

TODO:
  - Should Hypergraph carry around a "hyperlink" set, where a hyperlink is a pair of type
  (β, Set α)?
    - Would sort of bypass the need for IsHyperedge
    - But then, how do you define the hyperlink set?
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


/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `hyperedgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.hyperedgeSet H

/-! ## Basic Hypergraph Definitions & Predicates-/

/--
Predicate to determine if a hyperedge `e` contains exactly the vertex subset `s : Set α`
-/
def IsHyperedge (H : Hypergraph α β) (e : β) (s : Set α) : Prop :=
  (∀ x ∈ s, x ∈ V(H) ∧ H.IsIncident x e) ∧ (∀ y ∈ V(H) \ s, ¬H.IsIncident y e)

/--
The set of all hyperedges `e ∈ E(H)` that a given vertex `x` is incident on
-/
def hyperedgesIncVertex (H : Hypergraph α β) (x : α) : Set β := {e | e ∈ E(H) ∧ H.IsIncident x e}

/--
We define the *vertex hyperedge set* as the set of subsets of `E(H)` that each vertex in `V(H)` is
incident upon
-/
def hyperedgesIncVertices (H : Hypergraph α β) : Set (Set β) :=
  { H.hyperedgesIncVertex x | x ∈ V(H) }

/--
The set of all vertices `x ∈ V(H)` that are incident on a hyperedge `e`
-/
def verticesIncHyperedge (H : Hypergraph α β) (e : β) : Set α := { x | x ∈ V(H) ∧ H.IsIncident x e}

/--
We define the *hyperedge vertex set* as the set of all subsets of `V(H)` that represent real
hyperedges in `E(H)`
-/
def verticesIncHyperedges (H : Hypergraph α β) : Set (Set α) :=
  {H.verticesIncHyperedge e | e ∈ E(H)}

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


/-! ## Common Example Hypergraphs -/

/--
The empty hypergraph

An empty hypergraph contains an empty vertex set and an empty hyperedge set
-/
def emptyHypergraph (α β : Type*) : Hypergraph α β := Hypergraph.mk ∅ ∅ (fun _ _ => False)

/--
A singleton hypergraph

A singleton hypergraph contains only one vertex and an empty hyperedge set
-/
def singletonHypergraph (α β : Type*) (x : α) : Hypergraph α β :=
  Hypergraph.mk {x} ∅ (fun _ _ => False)


/-! ## Additional Predicates -/

/--
Predicate to determine if a vertex is isolated, meaning that it is not incident on any hyperedges.
Note that this includes loops, i.e., if vertex `x` is isolated, there is no hyperedge with
associated vertex subset `{x}`
-/
def IsIsolated (H : Hypergraph α β) (x : α) : Prop :=
  ∀ e ∈ E(H), ¬H.IsIncident x e

/--
Predicate to determine if a hyperedge `e` is a loop, meaning that its associated vertex subset `s`
contains only one vertex, i.e., `|s| = 1`

TODO: am I using Set.encard right?
-/
def IsLoop (H : Hypergraph α β) (e : β) (s : Set α) : Prop :=
  H.IsHyperedge e s ∧ (Set.encard s) = 1

/--
Predicate to determine if a hypergraph is empty
-/
def IsEmpty (H : Hypergraph α β) : Prop := V(H) = ∅ ∧ E(H) = ∅

/--
Predicate to determine if a hypergraph is trivial

A hypergraph is trivial if it has a nonempty vertex set and an empty hyperedge set
-/
def IsTrivial (H : Hypergraph α β) : Prop := Nonempty V(H) ∧ E(H) = ∅

/--
Predicate to determine is a hypergraph `H` is complete, meaning that each member of the power set of
the vertices (`𝒫 V(H)`) is represented in `E(H)`
-/
def IsComplete (H : Hypergraph α β) : Prop :=
  ∀ s ∈ 𝒫 V(H), ∃ e ∈ E(H), H.IsHyperedge e s

/--
Predicate to determine if a hypergraph is simple

A simple hypergraph is one in which, for each hyperedge `e ∈ E(H)` (with associated vertex subset
`s : Set α`), there is no other hyperedge `f ∈ E(H)` (with associated vertex subset `t : Set α`)
such that `s ⊂ t`.
-/
def IsSimple (H : Hypergraph α β) : Prop :=
  ∀ s ∈ H.verticesIncHyperedges, ∀ t ∈ H.verticesIncHyperedges \ {s}, ¬s ⊆ t


/-! ## Cardinality -/

/--
The *order* of a hypergraph `H` is defined as the number of vertices contained in `H`
-/
noncomputable def order (H : Hypergraph α β) : ENat := Set.encard V(H)

/--
The *size* of a hypergraph `H` is defined as the number of hyperedges contained in `H`
-/
noncomputable def size (H : Hypergraph α β) : ENat := Set.encard E(H)

/--
The set of vertex *degrees* of a hypergraph `H`.

A vertex `x` has degree `n`, where `n` is the number of hyperedges in `E(H)` that `x` is incident
on.
-/
noncomputable def vertexDegrees (H : Hypergraph α β) : Set ENat :=
  {Set.encard l | l ∈ H.hyperedgesIncVertices}

/--
The set of hyperedge *degrees* of a hypergraph `H`.

A hyperedge `e` has degree `n`, where `n` is the number of vertices in `V(H)` that are incident on
`e`.
-/
noncomputable def hyperedgeDegrees (H : Hypergraph α β) : Set ENat :=
  {Set.encard s | s ∈ H.verticesIncHyperedges}


/-! ## Hypergraph Dual -/

/--
The *dual* of a hypergraph `H` is the hypergraph `H*`, where
  - `H*.vertexSet = H.hyperedgeSet`
  - `H*.hyperedgeSet = H.vertexSet`
  - `H*.IsIncident e x ↔ H.IsIncident x e` (this will be proven)
-/
def dual (H : Hypergraph α β) : Hypergraph β α :=
  Hypergraph.mk H.hyperedgeSet H.vertexSet (fun e x => H.IsIncident x e)

/-- `H*` denotes the `dual` of a hypergraph `H` -/
scoped notation H "*" => Hypergraph.hyperedgeSet H

/-! ## Subhypergraphs, Partial Hypergraphs, and Section Hypergraphs -/

/--
Given a subset of the vertex set `V(H)` of a hypergraph `H` (`s : Set α`), the
*subhypergraph* `Hₛ` has `V(Hₛ) = s ∩ V(H)`, `E(Hₛ)` is the subset of `E(H)` for which all incident
vertices are included in `s`, and the incidence relation is the same as `H.IsIncident`
-/
def subHypergraph (H : Hypergraph α β) (s : Set α) :=
  Hypergraph.mk (s ∩ V(H)) {e | e ∈ E(H) ∧ H.verticesIncHyperedge e ⊆ s} H.IsIncident

-- TODO: induced subhypergraph (see Bretto pg. 2)
-- Definition is kind of messy, since you take subsets of each hyperedge, rather than only keeping
-- Allowed hyperedges


/--
Given a subset of the hyperedge set `E(H)` of a hypergraph `H` (`l : Set β`), the
*partial hypergraph* `Hˡ` has `E(Hˡ) = l ∩ E(H)`, `E(Hˡ)` is the subset of `V(H)` which is incident
on at least one hyperedge in `E(Hˡ)`, and the incidence relation is the same as `H.IsIncident`

Note: alternative definition of `vertexSet` of a partial hypergraph:
  {x | x ∈ V(H) ∧ Set.encard (H.hyperedgesIncVertex x ∩ l) ≥ 1}
-/
def partialHypergraph (H : Hypergraph α β) (l : Set β) :=
  Hypergraph.mk {x | x ∈ V(H) ∧ ∃ e ∈ l, H.IsIncident x e} (l ∩ E(H)) H.IsIncident

end Hypergraph
