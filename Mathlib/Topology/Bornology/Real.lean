/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Bornology

/-!
# The reals are equipped with their order bornology

This file contains results related to the order bornology on (non-negative) real numbers.
We prove that `ℝ` and `ℝ≥0` are equipped with the order topology and bornology.
-/

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

open Metric Set

instance instIsOrderBornology : IsOrderBornology ℝ where
  isBounded_iff_bddBelow_bddAbove s := by
    refine ⟨fun bdd ↦ ?_, fun h ↦ isBounded_of_bddAbove_of_bddBelow h.2 h.1⟩
    obtain ⟨r, hr⟩ : ∃ r : ℝ, s ⊆ Icc (-r) r := by
      simpa [Real.closedBall_eq_Icc] using bdd.subset_closedBall 0
    exact ⟨bddBelow_Icc.mono hr, bddAbove_Icc.mono hr⟩

namespace NNReal

/-!
Every instance is inherited from the corresponding structures on the reals.
-/

instance : OrderTopology ℝ≥0 :=
  orderTopology_of_ordConnected (t := Ici 0)

-- TODO: generalize this to a broader class of subtypes
instance : IsOrderBornology ℝ≥0 where
  isBounded_iff_bddBelow_bddAbove s := by
    refine ⟨fun bdd ↦ ?_, fun h ↦ isBounded_of_bddAbove_of_bddBelow h.2 h.1⟩
    obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, s ⊆ Icc 0 r := by
      obtain ⟨rreal, hrreal⟩ := bdd.subset_closedBall 0
      use rreal.toNNReal
      simp only [← NNReal.closedBall_zero_eq_Icc', Real.coe_toNNReal']
      exact subset_trans hrreal (Metric.closedBall_subset_closedBall (le_max_left rreal 0))
    exact ⟨bddBelow_Icc.mono hr, bddAbove_Icc.mono hr⟩

end NNReal
