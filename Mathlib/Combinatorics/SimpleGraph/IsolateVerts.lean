/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Isolate Vertices

This file defines the operation of isolating a set of vertices in a simple graph.

## Main definitions

* `SimpleGraph.isolateVerts`: The graph obtained by isolating a set of vertices.

## TODO

* Once the `graph-on-a-set` refactor lands, replace `isolateVerts` with
  `induce` and remove this file.
-/

@[expose] public section

namespace SimpleGraph
variable {V : Type*} (G : SimpleGraph V) (s : Set V)

/-- `G.isolateVerts s` is the graph where all vertices in `s` are isolated. -/
def isolateVerts : SimpleGraph V where
  Adj u v := u ∉ s ∧ v ∉ s ∧ G.Adj u v
  symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩

@[simp]
lemma isolateVerts_empty : G.isolateVerts ∅ = G := by
  ext; simp [isolateVerts]

@[simp]
lemma isolateVerts_bot : (⊥ : SimpleGraph V).isolateVerts s = ⊥ := by
  ext; simp [isolateVerts]

@[simp]
lemma isolateVerts_le : G.isolateVerts s ≤ G :=
  fun _ _ h ↦ h.2.2

@[simp]
lemma isolateVerts_singleton (v : V) : G.isolateVerts {v} = G.deleteIncidenceSet v := by
  ext; simp [isolateVerts, deleteIncidenceSet_adj]; tauto

end SimpleGraph
