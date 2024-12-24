/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.Graph.Classes
import Mathlib.Data.Fintype.Card

/-! ### Graph homomorphisms

We define graph homomorphisms for types with a `HasAdj` instance.
They are functions on vertices that send the `Adj` relation from the source
graph to the target graph.
As such, these sorts of graph homomorphisms are most appropriate for graphs without multiple edges.

## Main definitions

* `Graph.Hom`, `Graph.Embedding`, and `Graph.Iso` for graph
  homomorphisms, graph embeddings, and
  graph isomorphisms. Note that a graph embedding is a stronger notion than an
  injective graph homomorphism, and its image is an induced subgraph.

## Notations

* `→g`, `↪g`, and `≃g` for graph homomorphisms, graph embeddings, and graph isomorphisms,
  respectively.

-/

namespace Graph
variable {Γ Γ' Γ'' : Type _} {V : Γ → Type u} {V' : Γ' → Type u'} {V'' : Γ'' → Type u''}
variable [HasAdj Γ V] [HasAdj Γ' V'] [HasAdj Γ'' V'']

/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom (G : Γ) (G' : Γ') := RelHom (Adj G) (Adj G')

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.Adj (f v) (f w) ↔ G.Adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding (G : Γ) (G' : Γ') := RelEmbedding (Adj G) (Adj G')

/-- A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso (G : Γ) (G' : Γ') := RelIso (Adj G) (Adj G')

@[inherit_doc] infixl:50 " →g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso

variable {G : Γ} {G' : Γ'} {G'' : Γ''}

namespace Hom

variable (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
protected abbrev id : G →g G := RelHom.id _

theorem map_adj {v w : V G} (h : Adj G v w) : Adj G' (f v) (f w) := f.map_rel' h

/-- Composition of graph homomorphisms. -/
protected abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' := RelHom.comp f' f

pp_extended_field_notation Hom.comp

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : (f'.comp f : V G → V'' G'') = f' ∘ f := rfl

end Hom

namespace Embedding

variable (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G := RelEmbedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' := f.toRelHom

theorem map_adj_iff {v w : V G} : Adj G' (f v) (f w) ↔ Adj G v w := f.map_rel_iff

/-- Composition of graph embeddings. -/
protected abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' := f.trans f'

pp_extended_field_notation Embedding.comp

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : (f'.comp f : V G → V'' G'') = f' ∘ f := rfl

end Embedding

namespace Iso

variable (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G := RelIso.refl _

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' := f.toRelEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' := f.toEmbedding.toHom

/-- The inverse of a graph isomorphism. -/
abbrev symm : G' ≃g G := RelIso.symm f

theorem map_adj_iff {v w : V G} : Adj G' (f v) (f w) ↔ Adj G v w := f.map_rel_iff

theorem card_eq_of_iso [Fintype (V G)] [Fintype (V' G')] (f : G ≃g G') :
    Fintype.card (V G) = Fintype.card (V' G') :=
  Fintype.card_congr f.toEquiv

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' := f.trans f'

pp_extended_field_notation Iso.comp

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : (f'.comp f : V G → V'' G'') = f' ∘ f := rfl

end Iso

end Graph
