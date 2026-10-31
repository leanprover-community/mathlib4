/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# Hypergraphs as graph-like structures

This file shows that `Hypergraph` is `HyperGraphLike`, `Undirected`, and `Loopless`, with incidence
identifiers of type `α × Set α` (a vertex paired with an edge containing it).
-/

public section

variable {α : Type*} {H : Hypergraph α}

open HyperGraphLike

namespace Hypergraph

@[simps]
instance : HyperGraphLike α (α × Set α) (Set α) (Hypergraph α) where
  verts H := V(H)
  edges H := E(H)
  IsIncident H i e v := i.2 ∈ E(H) ∧ i.1 ∈ i.2 ∧ i.2 = e ∧ i.1 = v
  IsSource H i := i.2 ∈ E(H) ∧ i.1 ∈ i.2
  IsTarget H i := i.2 ∈ E(H) ∧ i.1 ∈ i.2
  vert_mem_of_isIncident H i e v hi := by
    obtain ⟨he, hv, rfl, rfl⟩ := hi
    exact mem_vertexSet_of_mem_edgeSet he hv
  edge_mem_of_isIncident H i e v hi := by grind
  eq_and_eq_of_isIncident_of_isIncident _ _ _ _ _ _ := by grind
  isIncident_iff H i := by grind
  Adj H := H.Adj
  adj_def H u v := by
    simp only [Adj, ↓existsAndEq, Prod.exists]
    grind

attribute [grind =] verts_def edges_def isSource_def isTarget_def isLink_def adj_def

instance : Undirected α (α × Set α) (Set α) (Hypergraph α) where
  isSource_iff G i := by simp

lemma edgeFun_eq {i : α × Set α} (hi : i.2 ∈ H.edgeSet) (hv : i.1 ∈ i.2) :
    edgeFun H i = Part.some i.2 := by
  ext e
  rw [mem_edgeFun_iff_exists_isIncident]
  simp [hi, hv, eq_comm]

lemma endPoint_eq {i : α × Set α} (hi : i.2 ∈ H.edgeSet) (hv : i.1 ∈ i.2) :
    endPoint H i = Part.some i.1 := by
  ext v
  rw [mem_endPoint_iff_exists_isIncident]
  simp [hi, hv, eq_comm]

instance : Loopless α (α × Set α) (Set α) (Hypergraph α) where
  no_loops_of_mem_mem H i j hi hj hij hne := by
    obtain ⟨_, _, he, hv, rfl, rfl⟩ := hi
    obtain ⟨_, _, hf, hw, rfl, rfl⟩ := hj
    grind [endPoint_eq, edgeFun_eq, Part.some_inj]

end Hypergraph
