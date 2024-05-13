/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Bounded
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

lemma dist_eq (x y : ℤ) : dist x y = |(x : ℝ) - y| := rfl
#align int.dist_eq Int.dist_eq

lemma dist_eq' (m n : ℤ) : dist m n = |m - n| := by rw [dist_eq]; norm_cast

@[norm_cast, simp]
lemma dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl
#align int.dist_cast_real Int.dist_cast_real

lemma pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n := by
  intro m n hne
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
#align int.pairwise_one_le_dist Int.pairwise_one_le_dist

lemma uniformEmbedding_coe_real : UniformEmbedding ((↑) : ℤ → ℝ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align int.uniform_embedding_coe_real Int.uniformEmbedding_coe_real

lemma closedEmbedding_coe_real : ClosedEmbedding ((↑) : ℤ → ℝ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align int.closed_embedding_coe_real Int.closedEmbedding_coe_real

instance : MetricSpace ℤ := Int.uniformEmbedding_coe_real.comapMetricSpace _

lemma preimage_ball (x : ℤ) (r : ℝ) : (↑) ⁻¹' ball (x : ℝ) r = ball x r := rfl
#align int.preimage_ball Int.preimage_ball

lemma preimage_closedBall (x : ℤ) (r : ℝ) : (↑) ⁻¹' closedBall (x : ℝ) r = closedBall x r := rfl
#align int.preimage_closed_ball Int.preimage_closedBall

lemma ball_eq_Ioo (x : ℤ) (r : ℝ) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball, Real.ball_eq_Ioo, preimage_Ioo]
#align int.ball_eq_Ioo Int.ball_eq_Ioo

lemma closedBall_eq_Icc (x : ℤ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
#align int.closed_ball_eq_Icc Int.closedBall_eq_Icc

instance : ProperSpace ℤ :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

@[simp]
lemma cobounded_eq : Bornology.cobounded ℤ = atBot ⊔ atTop := by
  simp_rw [← comap_dist_right_atTop (0 : ℤ), dist_eq', sub_zero,
    ← comap_abs_atTop, ← @Int.comap_cast_atTop ℝ, comap_comap]; rfl

@[deprecated] alias cocompact_eq := cocompact_eq_atBot_atTop -- deprecated on 2024-02-07
#align int.cocompact_eq Int.cocompact_eq

@[simp]
lemma cofinite_eq : (cofinite : Filter ℤ) = atBot ⊔ atTop := by
  rw [← cocompact_eq_cofinite, cocompact_eq_atBot_atTop]
#align int.cofinite_eq Int.cofinite_eq

end Int
