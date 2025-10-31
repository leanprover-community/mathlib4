/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!

# Graph Orientation

This module introduces conversion operations between `Digraph`s and `SimpleGraph`s, by forgetting
the edge orientations of `Digraph`.

## Main Definitions

- `Digraph.toSimpleGraphInclusive`: Converts a `Digraph` to a `SimpleGraph` by creating an
  undirected edge if either orientation exists in the digraph.
- `Digraph.toSimpleGraphStrict`: Converts a `Digraph` to a `SimpleGraph` by creating an undirected
  edge only if both orientations exist in the digraph.

## TODO

- Show that there is an isomorphism between loopless complete digraphs and oriented graphs.
- Define more ways to orient a `SimpleGraph`.
- Provide lemmas on how `toSimpleGraphInclusive` and `toSimpleGraphStrict` relate to other lattice
  structures on `SimpleGraph`s and `Digraph`s.

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
lemma toSimpleGraphInclusive_mono : Monotone (toSimpleGraphInclusive : _ → SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ ↦ ⟨h₂.1, h₂.2.imp (h₁ _ _) (h₁ _ _)⟩

@[mono]
lemma toSimpleGraphStrict_mono : Monotone (toSimpleGraphStrict : _ → SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ ↦ ⟨h₂.1, h₁ _ _ h₂.2.1, h₁ _ _ h₂.2.2⟩

@[simp]
lemma toSimpleGraphInclusive_top : (⊤ : Digraph V).toSimpleGraphInclusive = ⊤ := by
  ext; exact ⟨And.left, fun h ↦ ⟨h.ne, Or.inl trivial⟩⟩

@[simp]
lemma toSimpleGraphStrict_top : (⊤ : Digraph V).toSimpleGraphStrict = ⊤ := by
  ext; exact ⟨And.left, fun h ↦ ⟨h.ne, trivial, trivial⟩⟩

@[simp]
lemma toSimpleGraphInclusive_bot : (⊥ : Digraph V).toSimpleGraphInclusive = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, False.elim⟩

@[simp]
lemma toSimpleGraphStrict_bot : (⊥ : Digraph V).toSimpleGraphStrict = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, False.elim⟩

end toSimpleGraph

end Digraph
