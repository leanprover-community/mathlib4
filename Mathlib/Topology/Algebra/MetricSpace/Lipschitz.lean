/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz continuous functions

This file develops Lipschitz continuous functions further with some results that depend on algebra.
-/

assert_not_exists Module.Basis Ideal

open Filter Set NNReal Metric

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}

lemma LipschitzWith.cauchySeq_comp {f : α → β} (hf : LipschitzWith K f) {u : ℕ → α}
    (hu : CauchySeq u) :
    CauchySeq (f ∘ u) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hu with ⟨b, b_nonneg, hb, blim⟩
  refine cauchySeq_iff_le_tendsto_0.2 ⟨fun n ↦ K * b n, ?_, ?_, ?_⟩
  · exact fun n ↦ mul_nonneg (by positivity) (b_nonneg n)
  · exact fun n m N hn hm ↦ hf.dist_le_mul_of_le (hb n m N hn hm)
  · rw [← mul_zero (K : ℝ)]
    exact blim.const_mul _

lemma LipschitzOnWith.cauchySeq_comp {s : Set α} {f : α → β} (hf : LipschitzOnWith K f s)
    {u : ℕ → α} (hu : CauchySeq u) (h'u : range u ⊆ s) :
    CauchySeq (f ∘ u) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hu with ⟨b, b_nonneg, hb, blim⟩
  refine cauchySeq_iff_le_tendsto_0.2 ⟨fun n ↦ K * b n, ?_, ?_, ?_⟩
  · exact fun n ↦ mul_nonneg (by positivity) (b_nonneg n)
  · intro n m N hn hm
    have A n : u n ∈ s := h'u (mem_range_self _)
    apply (hf.dist_le_mul _ (A n) _ (A m)).trans
    exact mul_le_mul_of_nonneg_left (hb n m N hn hm) K.2
  · rw [← mul_zero (K : ℝ)]
    exact blim.const_mul _

/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
theorem continuousAt_of_locally_lipschitz {f : α → β} {x : α} {r : ℝ} (hr : 0 < r) (K : ℝ)
    (h : ∀ y, dist y x < r → dist (f y) (f x) ≤ K * dist y x) : ContinuousAt f x := by
  -- We use `h` to squeeze `dist (f y) (f x)` between `0` and `K * dist y x`
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (mem_of_superset (ball_mem_nhds _ hr) h) ?_)
  -- Then show that `K * dist y x` tends to zero as `y → x`
  refine (continuous_const.mul (continuous_id.dist continuous_const)).tendsto' _ _ ?_
  simp
