/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Local graph operations

This file defines some single-graph operations that modify a finite number of vertices
and proves basic theorems about them. When the graph itself has a finite number of vertices
we also prove theorems about the number of edges in the modified graphs.

## Main definitions

* `G.replaceVertex s t` is `G` with `t` replaced by a copy of `s`,
  removing the `s-t` edge if present.
-/


open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s t : V)

section ReplaceVertex

/-- The graph formed by forgetting `t`'s neighbours and instead giving it those of `s`. The `s-t`
edge is removed if present. -/
abbrev replaceVertex : SimpleGraph V where
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm v w := by dsimp only; split_ifs <;> simp [adj_comm]

/-- There is never an `s-t` edge in `G.replaceVertex s t`. -/
theorem not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t := by simp

@[simp]
theorem replaceVertex_self : G.replaceVertex s s = G := by
  ext; dsimp only; split_ifs <;> simp_all [adj_comm]

/-- Except possibly for `t`, the neighbours of `s` in `G.replaceVertex s t` are its neighbours in
`G`. -/
lemma adj_replaceVertex_iff_of_ne_left {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj s w ↔ G.Adj s w := by simp [hw]

/-- Except possibly for itself, the neighbours of `t` in `G.replaceVertex s t` are the neighbours of
`s` in `G`. -/
lemma adj_replaceVertex_iff_of_ne_right {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj t w ↔ G.Adj s w := by simp [hw]

/-- Adjacency in `G.replaceVertex s t` which does not involve `t` is the same as that of `G`. -/
lemma adj_replaceVertex_iff_of_ne {v w : V} (hv : v ≠ t) (hw : w ≠ t) :
    (G.replaceVertex s t).Adj v w ↔ G.Adj v w := by simp [hv, hw]

end ReplaceVertex
