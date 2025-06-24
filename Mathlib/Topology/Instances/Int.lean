/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.MetricSpace.Basic

/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Filter Metric Set Topology

namespace Int

instance : Dist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℤ) : dist x y = |(x : ℝ) - y| := rfl

theorem dist_eq' (m n : ℤ) : dist m n = |m - n| := by rw [dist_eq]; norm_cast

@[norm_cast, simp]
theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl

theorem pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n := by
  intro m n hne
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]

theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : ℤ → ℝ) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

theorem isClosedEmbedding_coe_real : IsClosedEmbedding ((↑) : ℤ → ℝ) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

instance : MetricSpace ℤ := Int.isUniformEmbedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℤ) (r : ℝ) : (↑) ⁻¹' ball (x : ℝ) r = ball x r := rfl

theorem preimage_closedBall (x : ℤ) (r : ℝ) : (↑) ⁻¹' closedBall (x : ℝ) r = closedBall x r := rfl

theorem ball_eq_Ioo (x : ℤ) (r : ℝ) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball, Real.ball_eq_Ioo, preimage_Ioo]

theorem closedBall_eq_Icc (x : ℤ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]

instance : ProperSpace ℤ :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

@[simp]
theorem cobounded_eq : Bornology.cobounded ℤ = atBot ⊔ atTop := by
  simp_rw [← comap_dist_right_atTop (0 : ℤ), dist_eq', sub_zero,
    ← comap_abs_atTop, ← @Int.comap_cast_atTop ℝ, comap_comap]; rfl


@[simp]
theorem cofinite_eq : (cofinite : Filter ℤ) = atBot ⊔ atTop := by
  rw [← cocompact_eq_cofinite, cocompact_eq_atBot_atTop]

end Int
