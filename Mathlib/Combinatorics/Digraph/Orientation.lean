/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Order.GaloisConnection

/-!

# Graph Orientation

This module introduces conversion operations between `Digraph`s and `SimpleGraph`s, by either
forgetting the edge orientations of `Digraph`, or adding such orientations on a `SimpleGraph`. It
also introduces oriented graphs.

## Main Definitions

- `Digraph.toSimpleGraphOr`: Converts a `Digraph` to a `SimpleGraph` by creating an undirected edge
  if either orientation exists in the digraph.
- `Digraph.toSimpleGraphAnd`: Converts a `Digraph` to a `SimpleGraph` by creating an undirected edge
  only if both orientations exist in the digraph.
- `Digraph.IsOriented`: A predicate that determines whether a digraph is oriented (no self-loops and
  no bidirectional edges).
- `SimpleGraph.toDigraph`: Converts a `SimpleGraph` to a `Digraph` by creating edges in both
  directions for each undirected edge.

## TODO

- Show that there is an isomorphism between loopless complete digraphs and oriented graphs.
- Define more ways to orient a `SimpleGraph`.

## Tags

digraph, simple graph, oriented graphs
-/

variable {V : Type*}

namespace Digraph

section toSimpleGraph

/-! ### Orientation-forgetting maps on digraphs -/

/--
Orientation-forgetting map from `Digraph` to `SimpleGraph` that gives an unoriented edge if
either orientation is present.
-/
def toSimpleGraphOr (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj

/--
Orientation-forgetting map from `Digraph` to `SimpleGraph` that gives an unoriented edge if
both orientations are present.
-/
def toSimpleGraphAnd (G : Digraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ G.Adj v w ∧ G.Adj w v
  symm _ _ h := And.intro h.1.symm h.2.symm
  loopless _ h := h.1 rfl

lemma toSimpleGraphAnd_subgraph_toSimpleGraphOr (G : Digraph V) :
    G.toSimpleGraphAnd ≤ G.toSimpleGraphOr :=
  fun _ _ h ↦ ⟨h.1, Or.inl h.2.1⟩

lemma toSimpleGraphOr_mono : Monotone (toSimpleGraphOr : _ → SimpleGraph V) := by
  intro _ _ h₁ _ _ h₂
  apply And.intro h₂.1
  cases h₂.2
  · exact Or.inl <| h₁ ‹_›
  · exact Or.inr <| h₁ ‹_›

lemma toSimpleGraphAnd_mono : Monotone (toSimpleGraphAnd : _ → SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ ↦ And.intro h₂.1 <| And.intro (h₁ h₂.2.1) (h₁ h₂.2.2)

lemma toSimpleGraphOr_top : (⊤ : Digraph V).toSimpleGraphOr = ⊤ := by
  ext; exact ⟨fun h ↦ h.1, fun h ↦ ⟨h.ne, Or.inl trivial⟩⟩

lemma toSimpleGraphAnd_top : (⊤ : Digraph V).toSimpleGraphAnd = ⊤ := by
  ext; exact ⟨fun h ↦ h.1, fun h ↦ ⟨h.ne, trivial, trivial⟩⟩

lemma toSimpleGraphOr_bot : (⊥ : Digraph V).toSimpleGraphOr = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, fun h ↦ h.elim⟩

lemma toSimpleGraphAnd_bot : (⊥ : Digraph V).toSimpleGraphAnd = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, fun h ↦ h.elim⟩

end toSimpleGraph

section IsOriented

/-! ### Oriented graphs  -/

/--
Oriented graphs are `Digraph`s that have no self-loops and no pair of vertices with edges in both
directions.
-/
def IsOriented (G : Digraph V) : Prop :=
  ∀ v w : V, ¬G.Adj v v ∧ ¬(G.Adj v w ∧ G.Adj w v)

lemma isOriented_toSimpleGraphAnd_eq_bot {G : Digraph V} (h : G.IsOriented) :
    G.toSimpleGraphAnd = ⊥ := by
  ext; exact ⟨fun a ↦ (h _ _).2 a.2, fun h ↦ h.elim⟩

end IsOriented

end Digraph

namespace SimpleGraph

/-! ### Digraphs constructed from simple graphs -/

/--
Orienting map that gives a `Digraph` from a `SimpleGraph` by giving two edges in opposite directions
to each adjacent vertices in the `SimpleGraph`.
-/
def toDigraph (G : SimpleGraph V) : Digraph V where
  Adj v w := G.Adj v w

@[mono]
lemma toDigraph_mono : Monotone (toDigraph : _ → Digraph V) :=
  fun _ _ h₁ _ _ h₂ ↦ h₁ h₂

instance : GaloisConnection toDigraph (Digraph.toSimpleGraphAnd : _ → SimpleGraph V) :=
  fun _ _ ↦ ⟨fun h₁ _ _ h₂ ↦ ⟨h₂.ne, h₁ h₂, h₁ h₂.symm⟩, fun h₁ _ _ h₂ ↦ (h₁ h₂).2.1⟩

end SimpleGraph
