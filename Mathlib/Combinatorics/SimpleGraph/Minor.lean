/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Contraction
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Simple graph minors

This file defines the notion of minor of a simple graph.

## Main definitions

* `SimpleGraph.IsMinor G G'`, `G ≼ G'` : a graph `G` is a minor of a graph `G'` if it is a
  contraction of a subgraph of `G'`.

-/

@[expose] public section

namespace SimpleGraph

variable {V V'}

/-- A graph `G` is a minor of a graph `G'` if it is a contraction of a subgraph of `G'`. -/
def IsMinor (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ K : Subgraph G', G ≼c K.coe

/-- Infix notation for graph minor. -/
infix:50 " ≼ " => IsMinor

end SimpleGraph
