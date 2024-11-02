/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!

# Graph Orientation

This module introduces conversion operations between `Digraph`s and `SimpleGraph`s, by either
forgetting the edge orientations of `Digraph`, or adding such orientations on a `SimpleGraph`. It
also introduces oriented graphs.

## Main Definitions

- `Digraph.toSimpleGraphInclusive`: Converts a `Digraph` to a `SimpleGraph` by creating an
  undirected edge if either orientation exists in the digraph.
- `Digraph.toSimpleGraphStrict`: Converts a `Digraph` to a `SimpleGraph` by creating an undirected
  edge only if both orientations exist in the digraph.
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
def toSimpleGraphInclusive (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj

/--
Orientation-forgetting map from `Digraph` to `SimpleGraph` that gives an unoriented edge if
both orientations are present.
-/
def toSimpleGraphStrict (G : Digraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ G.Adj v w ∧ G.Adj w v
  symm _ _ h := And.intro h.1.symm h.2.symm
  loopless _ h := h.1 rfl

lemma toSimpleGraphStrict_subgraph_toSimpleGraphInclusive (G : Digraph V) :
    G.toSimpleGraphStrict ≤ G.toSimpleGraphInclusive :=
  fun _ _ h ↦ ⟨h.1, Or.inl h.2.1⟩

@[mono]
lemma toSimpleGraphInclusive_mono : Monotone (toSimpleGraphInclusive : _ → SimpleGraph V) := by
  intro _ _ h₁ _ _ h₂
  apply And.intro h₂.1
  cases h₂.2
  · exact Or.inl <| h₁ ‹_›
  · exact Or.inr <| h₁ ‹_›

@[mono]
lemma toSimpleGraphStrict_mono : Monotone (toSimpleGraphStrict : _ → SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ ↦ And.intro h₂.1 <| And.intro (h₁ h₂.2.1) (h₁ h₂.2.2)

lemma toSimpleGraphInclusive_top : (⊤ : Digraph V).toSimpleGraphInclusive = ⊤ := by
  ext; exact ⟨And.left, fun h ↦ ⟨h.ne, Or.inl trivial⟩⟩

lemma toSimpleGraphStrict_top : (⊤ : Digraph V).toSimpleGraphStrict = ⊤ := by
  ext; exact ⟨And.left, fun h ↦ ⟨h.ne, trivial, trivial⟩⟩

lemma toSimpleGraphInclusive_bot : (⊥ : Digraph V).toSimpleGraphInclusive = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, False.elim⟩

lemma toSimpleGraphStrict_bot : (⊥ : Digraph V).toSimpleGraphStrict = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, False.elim⟩

end toSimpleGraph
