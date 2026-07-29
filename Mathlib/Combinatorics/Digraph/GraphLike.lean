/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-!
# Digraphs as graph-like structures

This file defines an ordered-pair incidence presentation of a `Digraph` and proves its graph-like
properties.
-/

public section

variable {V : Type*} {G : Digraph V}

open HypergraphPresentation

namespace Digraph

/-- The presentation of a digraph whose edges are ordered vertex pairs and whose incidences record
whether they are the source or target incidence. -/
@[expose, simps]
def orderedPairPresentation (G : Digraph V) :
    HypergraphPresentation V (Bool × V × V) (V × V) G where
  verts := Set.univ
  edges := { (u, v) | G.Adj u v }
  IsIncident i e v := G.Adj e.1 e.2 ∧ i.2 = e ∧ if i.1 then e.1 = v else e.2 = v
  IsSource i := i.1 ∧ G.Adj i.2.1 i.2.2
  IsTarget i := ¬ i.1 ∧ G.Adj i.2.1 i.2.2
  vert_mem_of_isIncident {_ _ v} _ := Set.mem_univ v
  edge_mem_of_isIncident {_ _ _} := by grind
  eq_and_eq_of_isIncident_of_isIncident {_ _ _ _ _} := by grind
  isIncident_iff {i} := by
    simp +contextual only [↓existsAndEq, true_and, exists_and_left, Bool.not_eq_true, iff_def,
      and_true, Bool.eq_true_or_eq_false_self, implies_true]
    rintro (⟨hi1, hi2⟩ | ⟨hi1, hi2⟩)
    · use hi2, i.2.1, by grind
    · use hi2, i.2.2, by grind
  Adj := G.Adj
  adj_def := by simp

attribute [grind =] verts_orderedPairPresentation edges_orderedPairPresentation
  isSource_orderedPairPresentation isTarget_orderedPairPresentation
  isLink_orderedPairPresentation adj_orderedPairPresentation

instance : GraphLike G.orderedPairPresentation where
  order_eq_two := by
    simp only [edges_orderedPairPresentation, Set.mem_ofPred_eq, order, Prod.forall]
    intro u v hab
    have h : (edgeFun G.orderedPairPresentation).preimage {(u, v)} =
        {(true, u, v), (false, u, v)} := by
      ext i
      simp only [PFun.mem_preimage, Set.mem_singleton_iff, mem_edgeFun_iff_exists_isIncident,
        isIncident_orderedPairPresentation, exists_and_left, exists_eq_left, hab, true_and,
        Set.mem_insert_iff]
      refine ⟨by grind, ?_⟩
      rintro (rfl | rfl) <;> simp
    rw [h]
    exact Set.encard_pair (by simp)
  exists_isSource_of_mem_edgeSet := by
    rintro ⟨u, v⟩ he
    simpa
  exists_isTarget_of_mem_edgeSet := by
    rintro ⟨u, v⟩ he
    simpa

instance : Directed G.orderedPairPresentation where
  not_isTarget_of_isSource := by simp_all

instance : NoParallelEdge G.orderedPairPresentation where
  edge_eq_of_isLink h h' := by grind [isIncident_orderedPairPresentation]

end Digraph
