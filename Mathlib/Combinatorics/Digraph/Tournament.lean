/-
Copyright (c) 2025 Jaafar Tanoukhi, Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaafar Tanoukhi, Rida Hamadani
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Digraph.Orientation

/-!

# Tournaments

In this file we define tournaments, which are digraphs with exactly one edge between any two
vertices.

We assume that tournaments are loopless.

-/

namespace Digraph

variable (V : Type*) (G : Digraph V)

/--
A tournament is a loopless digraph such that any two vertices have exactly one edge between them.
-/
structure IsTournament : Prop where
  loopless w : ¬ G.Adj w w
  one_edge w v : w ≠ v → (G.Adj w v ↔ ¬ G.Adj v w)

theorem isOrientation_of_isTournament (G : Digraph V) (h : G.IsTournament) :
    G.IsOrientation ⊤ := by
  intro v w
  refine ⟨fun hT ↦ ?_, fun h ↦ ?_⟩
  · rw [h.one_edge w v hT]
    tauto
  · rw [SimpleGraph.top_adj, ne_eq]
    by_contra hc
    rw [hc] at h
    tauto

end Digraph
