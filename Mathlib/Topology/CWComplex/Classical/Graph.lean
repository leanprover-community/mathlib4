/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# 1-skeletons of CW complexes as graphs

In this file we define the 1-skeleton of a CW complex as a graph.

## Main definitions
* `CWComplex.OneSkeletonGraph`: the 1-skeleton of a CW complex as a graph.

-/

public section

open Metric Set Graph

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- The 1-skeleton of a CW complex as a graph. -/
@[expose, simps]
def CWComplex.OneSkeletonGraph (C : Set X) [CWComplex C] : Graph (cell C 0) (cell C 1) where
  vertexSet := univ
  edgeSet := univ
  IsLink e x y := cellFrontier 1 e = closedCell 0 x ∪ closedCell 0 y
  isLink_symm _ _ x y h := by grind
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    simp_rw [closedCell_zero_eq_singleton] at h1 h2
    rw [h1] at h2
    simp only [(RelCWComplex.injective_map_zero C).eq_iff, union_singleton, pair_eq_pair_iff] at h2
    tauto
  left_mem_of_isLink _ _ _ _ := mem_univ _
  edge_mem_iff_exists_isLink e := by
    simp only [mem_univ, true_iff]
    exact exists_cellFrontier_one_eq e

namespace CWComplex.OneSkeletonGraph

variable {C : Set X} [CWComplex C]

lemma isLink_iff_pair (e : cell C 1) (x y : cell C 0) :
    (OneSkeletonGraph C).IsLink e x y ↔ cellFrontier 1 e = {map 0 x ![], map 0 y ![]} := by
  rw [OneSkeletonGraph_isLink, closedCell_zero_eq_singleton, closedCell_zero_eq_singleton,
    singleton_union]

lemma exists_isLoopAt_iff (e : cell C 1) : (∃ x : cell C 0, (OneSkeletonGraph C).IsLoopAt e x) ↔
      ∃ x : cell C 0, cellFrontier 1 e = closedCell 0 x := by
  refine exists_congr fun x ↦ ?_
  change cellFrontier 1 e = closedCell 0 x ∪ closedCell 0 x ↔ _
  rw [union_self]

lemma exists_isLoopAt_iff_subsingleton (e : cell C 1) :
    (∃ x : cell C 0, (OneSkeletonGraph C).IsLoopAt e x) ↔ (cellFrontier 1 e).Subsingleton := by
  rw [exists_isLoopAt_iff]
  refine ⟨fun ⟨x, hx⟩ => by simp [closedCell_zero_eq_singleton, hx], fun h => ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_cellFrontier_one_eq e
  simp only [closedCell_zero_eq_singleton, union_singleton] at hxy
  obtain rfl : x = y := RelCWComplex.injective_map_zero C <| (hxy ▸ h) (by simp) (by simp)
  exact ⟨x, by simp [hxy, closedCell_zero_eq_singleton]⟩

lemma not_exists_isLoopAt_iff_nontrivial (e : cell C 1) :
    ¬(∃ x : cell C 0, (OneSkeletonGraph C).IsLoopAt e x) ↔ (cellFrontier 1 e).Nontrivial :=
  (exists_isLoopAt_iff_subsingleton e).not.trans not_subsingleton_iff

@[simp]
lemma adj_iff (x y : cell C 0) : (OneSkeletonGraph C).Adj x y ↔
    ∃ e : cell C 1, cellFrontier 1 e = closedCell 0 x ∪ closedCell 0 y := Iff.rfl

end CWComplex.OneSkeletonGraph

end Topology
