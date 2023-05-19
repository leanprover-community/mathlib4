/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.ProjectionNotation

/-! # `HasAdj` class for types with an associated relation called `Adj`

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

/--
Axiom that the adjacency relation is symmetric.
-/
class IsAdjSymmetric (Γ : Type _) (V : outParam (Γ → Type _)) [HasAdj Γ V] : Prop where
  adj_symmetric (G : Γ) : Symmetric (HasAdj.Adj G)
#align simple_graph.symm IsAdjSymmetric.adj_symmetric

protected theorem HasAdj.Adj.symm [HasAdj Γ V] [IsAdjSymmetric Γ V]
    (G : Γ) (u v : V G) (h : Adj G u v) : Adj G v u :=
  IsAdjSymmetric.adj_symmetric G h
#align simple_graph.adj.symm HasAdj.Adj.symm

/--
Axiom that the adjacency relation has no loop edges (i.e., if it is irreflexive).
-/
class IsAdjIrreflexive (Γ : Type _) (V : outParam (Γ → Type _)) [HasAdj Γ V] : Prop where
  adj_irreflexive (G : Γ) : Irreflexive (HasAdj.Adj G)
#align simple_graph.loopless IsAdjIrreflexive.adj_irreflexive

protected theorem HasAdj.Adj.loopless [HasAdj Γ V] [IsAdjIrreflexive Γ V]
    {G : Γ} {u : V G} : ¬ Adj G u u := IsAdjIrreflexive.adj_irreflexive G _

protected theorem HasAdj.Adj.ne [HasAdj Γ V] [IsAdjIrreflexive Γ V]
    {G : Γ} {u v : V G} (h : Adj G u v) : u ≠ v | rfl => h.loopless
#align simple_graph.adj.ne HasAdj.Adj.ne

namespace Graph

/-! ### The `Graph` namespace

We put general things having to do with graphs into the `Graph` namespace.
-/

export HasAdj (Adj)
export IsAdjSymmetric (adj_symmetric)
export IsAdjIrreflexive (adj_irreflexive)

variable {Γ : Type _} {V : Γ → Type _} [HasAdj Γ V]

section symmetric
variable [IsAdjSymmetric Γ V] (G : Γ)

theorem adj_symm {u v : V G} (h : Adj G u v) : Adj G v u := h.symm
#align simple_graph.adj_symm Graph.adj_symm

theorem adj_comm {u v : V G} : Adj G u v ↔ Adj G v u := (adj_symmetric G).iff u v
#align simple_graph.adj_comm Graph.adj_comm

end symmetric

section irreflexive
variable [IsAdjIrreflexive Γ V] (G : Γ)

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
