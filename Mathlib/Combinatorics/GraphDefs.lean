/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.ProjectionNotation

/-! # Basic definitions for graph structures

This module contains definitions that are common to different kinds of (simple) graphs,
in particular combinatorial objects that are fundamentally some kind of relation.

We put general things having to do with graphs into the `Graph` namespace.

## Main definitions

* `Graph.HasAdj` is a typeclass that imbues terms of a type with an adjacency relation.
  This is like an indexed family of `Prop`-valued `Quiver`s.

* `Graph.IsAdjSymmetric` and `Graph.IsAdjIrreflexive` restrict the graphs under consideration
  to those that are symmetric or irreflexive. Simple graphs are modeled as graphs satisfying both,
  and `SimpleGraph` is a type modeling this.

* `Graph.Dart` is an ordered pair of adjacent vertices, thought of as being an
  orientated edge. These are also known as "half-edges" or "bonds."

* `Graph.Hom`, `Graph.Embedding`, and `Graph.Iso` for graph
  homomorphisms, graph embeddings, and
  graph isomorphisms. Note that a graph embedding is a stronger notion than an
  injective graph homomorphism, since its image is an induced subgraph.

## Notations

* `→g`, `↪g`, and `≃g` for graph homomorphisms, graph embeddings, and graph isomorphisms,
  respectively.

-/

namespace Graph

/-! ### `HasAdj` class for types with an associated relation called `Adj`

The `HasAdj` class gives the structure of a (simple) directed graph to
each term of a given type by providing an `Adj` relation.

TODO: Better name? Maybe `DigraphLike`? `HasAdj` is nice and short though.
-/

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

section Maps

/-! ### Graph homomorphisms

We define graph homomorphisms for types with a `HasAdj` instance.
These make sense for graphs without multiple edges.
-/

variable {Γ Γ' Γ'' : Type _} {V : Γ → Type u} {V' : Γ' → Type u'} {V'' : Γ'' → Type u''}
variable [HasAdj Γ V] [HasAdj Γ' V'] [HasAdj Γ'' V'']

/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom (G : Γ) (G' : Γ') := RelHom (Adj G) (Adj G')
#align simple_graph.hom Graph.Hom

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.Adj (f v) (f w) ↔ G.Adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding (G : Γ) (G' : Γ') := RelEmbedding (Adj G) (Adj G')
#align simple_graph.embedding Graph.Embedding

/-- A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso (G : Γ) (G' : Γ') := RelIso (Adj G) (Adj G')
#align simple_graph.iso Graph.Iso

infixl:50 " →g " => Hom
infixl:50 " ↪g " => Embedding
infixl:50 " ≃g " => Iso

variable {G : Γ} {G' : Γ'} {G'' : Γ''}

namespace Hom

variable (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
protected abbrev id : G →g G := RelHom.id _
#align simple_graph.hom.id Graph.Hom.id

theorem map_adj {v w : V G} (h : Adj G v w) : Adj G' (f v) (f w) := f.map_rel' h
#align simple_graph.hom.map_adj Graph.Hom.map_adj

/-- Composition of graph homomorphisms. -/
protected abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' := RelHom.comp f' f
#align simple_graph.hom.comp Graph.Hom.comp

pp_extended_field_notation Hom.comp

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : (f'.comp f : V G → V'' G'') = f' ∘ f := rfl
#align simple_graph.hom.coe_comp Graph.Hom.coe_comp

end Hom

namespace Embedding

variable (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G := RelEmbedding.refl _
#align simple_graph.embedding.refl Graph.Embedding.refl

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' := f.toRelHom
#align simple_graph.embedding.to_hom Graph.Embedding.toHom

theorem map_adj_iff {v w : V G} : Adj G' (f v) (f w) ↔ Adj G v w := f.map_rel_iff
#align simple_graph.embedding.map_adj_iff Graph.Embedding.map_adj_iff

/-- Composition of graph embeddings. -/
protected abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' := f.trans f'
#align simple_graph.embedding.comp Graph.Embedding.comp

pp_extended_field_notation Embedding.comp

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : (f'.comp f : V G → V'' G'') = f' ∘ f := rfl
#align simple_graph.embedding.coe_comp Graph.Embedding.coe_comp

end Embedding

namespace Iso

variable (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G := RelIso.refl _
#align simple_graph.iso.refl Graph.Iso.refl

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' := f.toRelEmbedding
#align simple_graph.iso.to_embedding Graph.Iso.toEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' := f.toEmbedding.toHom
#align simple_graph.iso.to_hom Graph.Iso.toHom

/-- The inverse of a graph isomorphism. -/
abbrev symm : G' ≃g G := RelIso.symm f
#align simple_graph.iso.symm Graph.Iso.symm

theorem map_adj_iff {v w : V G} : Adj G' (f v) (f w) ↔ Adj G v w := f.map_rel_iff
#align simple_graph.iso.map_adj_iff Graph.Iso.map_adj_iff

theorem card_eq_of_iso [Fintype (V G)] [Fintype (V' G')] (f : G ≃g G') :
    Fintype.card (V G) = Fintype.card (V' G') :=
  Fintype.card_congr f.toEquiv
#align simple_graph.iso.card_eq_of_iso Graph.Iso.card_eq_of_iso

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' := f.trans f'
#align simple_graph.iso.comp Graph.Iso.comp

pp_extended_field_notation Iso.comp

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : (f'.comp f : V G → V'' G'') = f' ∘ f := rfl
#align simple_graph.iso.coe_comp Graph.Iso.coe_comp

end Iso

end Maps

/-! ## Darts -/

/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
structure Dart (G : Γ) extends (V G) × (V G) where
  is_adj : Adj G fst snd
#align simple_graph.dart Graph.Dart

initialize_simps_projections Dart (+toProd, -fst, -snd)

pp_extended_field_notation Dart

section Darts

variable {G : Γ}

theorem Dart.ext_iff (d₁ d₂ : Dart G) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp
#align simple_graph.dart.ext_iff Graph.Dart.ext_iff

@[ext]
theorem Dart.ext (d₁ d₂ : Dart G) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (Dart.ext_iff d₁ d₂).mpr h
#align simple_graph.dart.ext Graph.Dart.ext

instance [DecidableEq (V G)] : DecidableEq (Dart G)
  | d₁, d₂ =>
    if h : d₁.toProd = d₂.toProd then
      isTrue (Dart.ext _ _ h)
    else
      isFalse (by rintro rfl; exact (h rfl).elim)

-- Porting note: deleted `Dart.fst` and `Dart.snd` since they are now invalid declaration names,
-- even though there is not actually a `SimpleGraph.Dart.fst` or `SimpleGraph.Dart.snd`.

theorem Dart.toProd_injective : Function.Injective (Dart.toProd : Dart G → V G × V G) := Dart.ext
#align simple_graph.dart.to_prod_injective Graph.Dart.toProd_injective

end Darts

end Graph
