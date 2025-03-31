/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Bornology.Hom
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lipschitz continuous functions
TODO
-/

assert_not_exists Basis Ideal

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

namespace LipschitzWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] {K : ℝ≥0} {f : α → β}
  {x y : α} {r : ℝ}

lemma cauchySeq_comp (hf : LipschitzWith K f) {u : ℕ → α} (hu : CauchySeq u) :
    CauchySeq (f ∘ u) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hu with ⟨b, b_nonneg, hb, blim⟩
  refine cauchySeq_iff_le_tendsto_0.2 ⟨fun n ↦ K * b n, ?_, ?_, ?_⟩
  · exact fun n ↦ mul_nonneg (by positivity) (b_nonneg n)
  · exact fun n m N hn hm ↦ hf.dist_le_mul_of_le (hb n m N hn hm)
  · rw [← mul_zero (K : ℝ)]
    exact blim.const_mul _

end Metric

end LipschitzWith

namespace Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s : Set α} {t : Set β}

end Metric

namespace LipschitzOnWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {K : ℝ≥0} {s : Set α} {f : α → β}

lemma cauchySeq_comp (hf : LipschitzOnWith K f s)
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

end Metric

end LipschitzOnWith

namespace LocallyLipschitz

end LocallyLipschitz

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}

/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
theorem continuousAt_of_locally_lipschitz {x : α} {r : ℝ} (hr : 0 < r) (K : ℝ)
    (h : ∀ y, dist y x < r → dist (f y) (f x) ≤ K * dist y x) : ContinuousAt f x := by
  -- We use `h` to squeeze `dist (f y) (f x)` between `0` and `K * dist y x`
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (mem_of_superset (ball_mem_nhds _ hr) h) ?_)
  -- Then show that `K * dist y x` tends to zero as `y → x`
  refine (continuous_const.mul (continuous_id.dist continuous_const)).tendsto' _ _ ?_
  simp
