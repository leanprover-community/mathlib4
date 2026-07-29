/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The standard simplex is compact

-/

public section

namespace Convexity.StdSimplex

section Real

lemma range_toFun_comp_weights_subset_closedBall (M : Type*) [Fintype M] :
    Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ) ⊆ Metric.closedBall 0 1 := by
  rintro _ ⟨x, rfl⟩
  simp [dist_pi_def, Real.nndist_eq]

lemma isBounded_range_toFun_comp_weights (M : Type*) [Finite M] :
    Bornology.IsBounded (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) := by
  have := Fintype.ofFinite M
  exact Bornology.IsBounded.subset Metric.isBounded_closedBall
    (range_toFun_comp_weights_subset_closedBall M)

lemma diam_range_toFun_comp_weights_subset_closedBall (M : Type*) [Fintype M] :
    Metric.diam (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) ≤ 1 :=
  Metric.diam_le_of_forall_dist_le (by simp) (by
    have (u : StdSimplex ℝ M) := u.weights_nonneg
    have (u : StdSimplex ℝ M) := u.weights_apply_le_one
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    simp [dist_pi_def, Real.nndist_eq, ← NNReal.coe_le_coe]
    grind)

lemma diam_range_toFun_comp_weights_subset_closedBall_eq_zero
    (M : Type*) [Fintype M] [Subsingleton M] :
    Metric.diam (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) = 0 :=
  Metric.diam_subsingleton (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    obtain rfl : x = y := by subsingleton
    simp)

open Classical in
lemma diam_range_toFun_comp_weights_subset_closedBall_eq_one
    (M : Type*) [Fintype M] [Nontrivial M] :
    Metric.diam (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) = 1 := by
  obtain ⟨x, y, h⟩ := exists_pair_ne M
  refine le_antisymm (diam_range_toFun_comp_weights_subset_closedBall M)
    (le_of_eq_of_le ((dist_pi_eq_iff (by simp)).mpr ⟨?_, fun z ↦ ?_⟩).symm
      (Metric.dist_le_diam_of_mem
        (isBounded_range_toFun_comp_weights _) (x := Pi.single x 1) (y := Pi.single y 1)
          ⟨.single x, by aesop⟩ ⟨.single y, by aesop⟩))
  · exact ⟨x, by simp [Pi.single_eq_of_ne h, Real.dist_eq]⟩
  · grind [Real.dist_eq]

end Real

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨x.weights_nonneg, x.weights_apply_le_one⟩

end Convexity.StdSimplex
