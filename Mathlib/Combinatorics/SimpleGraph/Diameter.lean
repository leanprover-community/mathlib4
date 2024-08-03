/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Lattice

/-!
# Diameter of a simple graph

This file defines the diameter of a simple graph as the greatest distance between any two vertices
in the graph.

## Main definitions

- `SimpleGraph.diam` is the graph diameter.

- `SimpleGraph.ediam` is the graph extended diameter.

## Todo

- Prove that `G.egirth ≤ 2 * G.ediam + 1` and `G.girth ≤ 2 * G.diam + 1` when the diameter is
  non-zero.

-/

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

/--
The extended diameter is the greatest distance between any two vertices, with the value `⊤` in
case the distances are not bounded above.
-/
noncomputable def ediam (G : SimpleGraph α) : ℕ∞ := ⨆ u v, G.edist u v


end SimpleGraph
