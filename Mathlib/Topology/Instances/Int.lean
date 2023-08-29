/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Int.Interval
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Archimedean

#align_import topology.instances.int from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Int

instance : Dist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℤ) : dist x y = |(x : ℝ) - y| := rfl
#align int.dist_eq Int.dist_eq

theorem dist_eq' (m n : ℤ) : dist m n = |m - n| := by rw [dist_eq]; norm_cast
                                                      -- ⊢ |↑m - ↑n| = ↑|m - n|
                                                                    -- 🎉 no goals

@[norm_cast, simp]
theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl
#align int.dist_cast_real Int.dist_cast_real

theorem pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n := by
  intro m n hne
  -- ⊢ 1 ≤ dist m n
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
  -- ⊢ 1 ≤ |↑m - ↑n|
                -- ⊢ 1 ≤ |m - n|
                           -- 🎉 no goals
#align int.pairwise_one_le_dist Int.pairwise_one_le_dist

theorem uniformEmbedding_coe_real : UniformEmbedding ((↑) : ℤ → ℝ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align int.uniform_embedding_coe_real Int.uniformEmbedding_coe_real

theorem closedEmbedding_coe_real : ClosedEmbedding ((↑) : ℤ → ℝ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align int.closed_embedding_coe_real Int.closedEmbedding_coe_real

instance : MetricSpace ℤ := Int.uniformEmbedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℤ) (r : ℝ) : (↑) ⁻¹' ball (x : ℝ) r = ball x r := rfl
#align int.preimage_ball Int.preimage_ball

theorem preimage_closedBall (x : ℤ) (r : ℝ) : (↑) ⁻¹' closedBall (x : ℝ) r = closedBall x r := rfl
#align int.preimage_closed_ball Int.preimage_closedBall

theorem ball_eq_Ioo (x : ℤ) (r : ℝ) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball, Real.ball_eq_Ioo, preimage_Ioo]
  -- 🎉 no goals
#align int.ball_eq_Ioo Int.ball_eq_Ioo

theorem closedBall_eq_Icc (x : ℤ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
  -- 🎉 no goals
#align int.closed_ball_eq_Icc Int.closedBall_eq_Icc

instance : ProperSpace ℤ :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    -- ⊢ IsCompact (Icc ⌈↑x - r⌉ ⌊↑x + r⌋)
    exact (Set.finite_Icc _ _).isCompact⟩
    -- 🎉 no goals

@[simp]
theorem cocompact_eq : cocompact ℤ = atBot ⊔ atTop := by
  simp_rw [← comap_dist_right_atTop_eq_cocompact (0 : ℤ), dist_eq', sub_zero,
    ← comap_abs_atTop, ← @Int.comap_cast_atTop ℝ, comap_comap]; rfl
                                                                -- 🎉 no goals
#align int.cocompact_eq Int.cocompact_eq

@[simp]
theorem cofinite_eq : (cofinite : Filter ℤ) = atBot ⊔ atTop := by
  rw [← cocompact_eq_cofinite, cocompact_eq]
  -- 🎉 no goals
#align int.cofinite_eq Int.cofinite_eq

end Int

