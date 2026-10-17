/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.DiHypergraph.Basic

/-!
# Dihypergraphs as graph-like structures

This file shows that `Dihypergraph` is `HyperGraphLike` and `Directed`, with incidence identifiers
of type `Bool × α × (Set α × Set α)` (a flag distinguishing source from target, a vertex, and an
edge containing that vertex on the corresponding side).
-/

public section

variable {α : Type*} {Dₕ : Dihypergraph α}

open HyperGraphLike

namespace Dihypergraph

@[simps]
instance : HyperGraphLike α (Bool × α × (Set α × Set α)) (Set α × Set α) (Dihypergraph α) where
  verts Dₕ := V(Dₕ)
  edges Dₕ := E(Dₕ)
  IsIncident Dₕ i e v :=
    i.2.2 ∈ E(Dₕ) ∧ i.2.2 = e ∧ i.2.1 = v ∧ if i.1 then v ∈ e.1 else v ∈ e.2
  IsSource Dₕ i := i.1 ∧ i.2.2 ∈ E(Dₕ) ∧ i.2.1 ∈ i.2.2.1
  IsTarget Dₕ i := ¬i.1 ∧ i.2.2 ∈ E(Dₕ) ∧ i.2.1 ∈ i.2.2.2
  vert_mem_of_isIncident Dₕ i e v := by
    rintro ⟨he, rfl, rfl, hv⟩
    grind [mem_vertexSet_of_mem_edgeSet_src, mem_vertexSet_of_mem_edgeSet_dst]
  edge_mem_of_isIncident Dₕ i e v hi := by grind
  eq_and_eq_of_isIncident_of_isIncident _ _ _ _ _ _ := by grind
  isIncident_iff Dₕ i := by grind

attribute [grind =] verts_def edges_def isSource_def isTarget_def isLink_def adj_def

instance : Directed α (Bool × α × (Set α × Set α)) (Set α × Set α) (Dihypergraph α) where
  not_isTarget_of_isSource _ _ hi ht := ht.1 hi.1

end Dihypergraph
