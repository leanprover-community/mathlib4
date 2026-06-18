/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fin.Basic

/-!
# Edge Coloring

This file defines edge colorings of simple graphs in terms of vertex colorings
of the line graph, and introduces the chromatic index.

## Main definitions

* `vizing.edgeColoring G α` — an `α`-edge-coloring of `G`, defined as a vertex
  coloring of `G.lineGraph`.
* `vizing.edgeColorable G n` — `G` is `n`-edge-colorable.
* `vizing.chromaticIndex G` — the chromatic index (minimum number of colors in a
  proper edge coloring), defined as the chromatic number of `G.lineGraph`.
-/

@[expose] public section

namespace vizing

variable {V : Type*} (G : SimpleGraph V) (α : Type*)

/-- The edge coloring of a graph is the vertex coloring of its line graph. -/
def edgeColoring := G.lineGraph.Coloring α

/-- A graph is edge colorable with `n` colors if its line graph is `n`-colorable. -/
def edgeColorable (n : ℕ) : Prop := G.lineGraph.Colorable n

/-- The chromatic index of `G` is the chromatic number of its line graph,
converted to a natural number (or 0 if infinite). -/
noncomputable def chromaticIndex : ℕ :=
  G.lineGraph.chromaticNumber.toNat

end vizing
