/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Instances.Real

/-!
# Topology on the rational numbers

The structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`.
-/


open Metric Set Filter

namespace Rat

instance : MetricSpace ℚ :=
  MetricSpace.induced (↑) Rat.cast_injective Real.metricSpace

theorem dist_eq (x y : ℚ) : dist x y = |(x : ℝ) - y| := rfl

@[norm_cast, simp]
theorem dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y :=
  rfl

theorem uniformContinuous_coe_real : UniformContinuous ((↑) : ℚ → ℝ) :=
  uniformContinuous_comap

theorem uniformEmbedding_coe_real : UniformEmbedding ((↑) : ℚ → ℝ) :=
  uniformEmbedding_comap Rat.cast_injective

theorem denseEmbedding_coe_real : DenseEmbedding ((↑) : ℚ → ℝ) :=
  uniformEmbedding_coe_real.denseEmbedding Rat.denseRange_cast

theorem embedding_coe_real : Embedding ((↑) : ℚ → ℝ) :=
  denseEmbedding_coe_real.to_embedding

theorem continuous_coe_real : Continuous ((↑) : ℚ → ℝ) :=
  uniformContinuous_coe_real.continuous

end Rat

@[norm_cast, simp]
theorem Nat.dist_cast_rat (x y : ℕ) : dist (x : ℚ) y = dist x y := by
  rw [← Nat.dist_cast_real, ← Rat.dist_cast]; congr

theorem Nat.uniformEmbedding_coe_rat : UniformEmbedding ((↑) : ℕ → ℚ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one <| by simpa using Nat.pairwise_one_le_dist

theorem Nat.closedEmbedding_coe_rat : ClosedEmbedding ((↑) : ℕ → ℚ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one <| by simpa using Nat.pairwise_one_le_dist

@[norm_cast, simp]
theorem Int.dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y := by
  rw [← Int.dist_cast_real, ← Rat.dist_cast]; congr

theorem Int.uniformEmbedding_coe_rat : UniformEmbedding ((↑) : ℤ → ℚ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one <| by simpa using Int.pairwise_one_le_dist

theorem Int.closedEmbedding_coe_rat : ClosedEmbedding ((↑) : ℤ → ℚ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one <| by simpa using Int.pairwise_one_le_dist

namespace Rat

instance : NoncompactSpace ℚ := Int.closedEmbedding_coe_rat.noncompactSpace

theorem uniformContinuous_add : UniformContinuous fun p : ℚ × ℚ => p.1 + p.2 :=
  Rat.uniformEmbedding_coe_real.toUniformInducing.uniformContinuous_iff.2 <| by
    simp only [Function.comp_def, Rat.cast_add]
    exact Real.uniformContinuous_add.comp
      (Rat.uniformContinuous_coe_real.prod_map Rat.uniformContinuous_coe_real)

theorem uniformContinuous_neg : UniformContinuous (@Neg.neg ℚ _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun h => by rw [dist_comm] at h; simpa only [dist_eq, cast_neg, neg_sub_neg] using h⟩

instance : UniformAddGroup ℚ :=
  UniformAddGroup.mk' Rat.uniformContinuous_add Rat.uniformContinuous_neg

instance : TopologicalAddGroup ℚ := inferInstance

instance : OrderTopology ℚ := induced_orderTopology _ Rat.cast_lt exists_rat_btwn

theorem uniformContinuous_abs : UniformContinuous (abs : ℚ → ℚ) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun h =>
      lt_of_le_of_lt (by simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

instance : TopologicalRing ℚ := inferInstance

nonrec theorem totallyBounded_Icc (a b : ℚ) : TotallyBounded (Icc a b) := by
  simpa only [preimage_cast_Icc]
    using totallyBounded_preimage Rat.uniformEmbedding_coe_real.toUniformInducing
      (totallyBounded_Icc (a : ℝ) b)

end Rat
