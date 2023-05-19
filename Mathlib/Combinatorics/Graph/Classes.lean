/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Rel

/-! # Typeclasses for graph structures

This module contains definitions that are common to different kinds of (simple) graphs,
in particular combinatorial objects that are fundamentally some kind of relation.

We put general things having to do with graphs into the `Graph` namespace.

## Main definitions

* `Graph.HasAdj` is a typeclass that imbues terms of a type with an adjacency relation.
  These model simple (directed) graphs.
  This is like an indexed family of `Prop`-valued `Quiver`s.

* `Graph.IsAdjSymmetric` and `Graph.IsAdjIrreflexive` restrict the graphs under consideration
  to those that are symmetric or irreflexive. Simple graphs are modeled as graphs satisfying both,
  and `SimpleGraph` is a type modeling this.

-/

namespace Graph

/--
Associates an *adjacency* relation to each term of `Γ`.
-/
class HasAdj (Γ : Type _) (V : outParam (Γ → Type _)) where
  /-- An adjacency relation for a term of type `Γ`. -/
  Adj (G : Γ) : V G → V G → Prop

export HasAdj (Adj)

/--
Axiom that the adjacency relation is symmetric.
-/
class IsAdjSymmetric (Γ : Type _) (V : outParam (Γ → Type _)) [HasAdj Γ V] : Prop where
  adj_symmetric (G : Γ) : Symmetric (HasAdj.Adj G)
#align simple_graph.symm Graph.IsAdjSymmetric.adj_symmetric

export IsAdjSymmetric (adj_symmetric)

/--
Axiom that the adjacency relation has no loop edges (i.e., if it is irreflexive).
-/
class IsAdjIrreflexive (Γ : Type _) (V : outParam (Γ → Type _)) [HasAdj Γ V] : Prop where
  adj_irreflexive (G : Γ) : Irreflexive (HasAdj.Adj G)
#align simple_graph.loopless Graph.IsAdjIrreflexive.adj_irreflexive

export IsAdjIrreflexive (adj_irreflexive)

variable {Γ : Type _} {V : Γ → Type _} [HasAdj Γ V]

section symmetric
variable [IsAdjSymmetric Γ V] (G : Γ)

protected theorem HasAdj.Adj.symm {G : Γ} {u v : V G} (h : Adj G u v) : Adj G v u :=
  IsAdjSymmetric.adj_symmetric G h
#align simple_graph.adj.symm Graph.HasAdj.Adj.symm

theorem adj_symm {u v : V G} (h : Adj G u v) : Adj G v u := h.symm
#align simple_graph.adj_symm Graph.adj_symm

theorem adj_comm {u v : V G} : Adj G u v ↔ Adj G v u := (adj_symmetric G).iff u v
#align simple_graph.adj_comm Graph.adj_comm

end symmetric

section irreflexive
variable [IsAdjIrreflexive Γ V] (G : Γ)

protected theorem HasAdj.Adj.loopless {G : Γ} {u : V G} : ¬ Adj G u u :=
  IsAdjIrreflexive.adj_irreflexive G _

protected theorem HasAdj.Adj.ne {G : Γ} {u v : V G} (h : Adj G u v) : u ≠ v
  | rfl => h.loopless
#align simple_graph.adj.ne Graph.HasAdj.Adj.ne

protected theorem HasAdj.Adj.ne' {G : Γ} {u v : V G} (h : Adj G u v) : v ≠ u
  | rfl => h.loopless
#align simple_graph.adj.ne' Graph.HasAdj.Adj.ne'

@[simp]
theorem adj_irrefl {u : V G} : ¬ Adj G u u | h => h.loopless
#align simple_graph.irrefl Graph.adj_irrefl

end irreflexive

end Graph
