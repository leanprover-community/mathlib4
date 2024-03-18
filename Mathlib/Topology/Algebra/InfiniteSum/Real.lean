/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real

#align_import topology.algebra.infinite_sum.real from "leanprover-community/mathlib"@"9a59dcb7a2d06bf55da57b9030169219980660cd"

/-!
# Infinite sum in the reals

This file provides lemmas about Cauchy sequences in terms of infinite sums.
-/

open Filter Finset BigOperators NNReal Topology

variable {α : Type*}

/-- If the extended distance between consecutive points of a sequence is estimated
by a summable series of `NNReal`s, then the original sequence is a Cauchy sequence. -/
theorem cauchySeq_of_edist_le_of_summable [PseudoEMetricSpace α] {f : ℕ → α} (d : ℕ → ℝ≥0)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : Summable d) : CauchySeq f := by
  refine EMetric.cauchySeq_iff_NNReal.2 fun ε εpos ↦ ?_
  -- Actually we need partial sums of `d` to be a Cauchy sequence
  replace hd : CauchySeq fun n : ℕ ↦ ∑ x in range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchySeq
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence
  refine (Metric.cauchySeq_iff'.1 hd ε (NNReal.coe_pos.2 εpos)).imp fun N hN n hn ↦ ?_
  specialize hN n hn
  -- We simplify the known inequality
  rw [dist_nndist, NNReal.nndist_eq, ← sum_range_add_sum_Ico _ hn, add_tsub_cancel_left,
    NNReal.coe_lt_coe, max_lt_iff] at hN
  rw [edist_comm]
  -- Then use `hf` to simplify the goal to the same form
  refine lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn fun _ _ ↦ hf _) ?_
  exact mod_cast hN.1
#align cauchy_seq_of_edist_le_of_summable cauchySeq_of_edist_le_of_summable

variable [PseudoMetricSpace α] {f : ℕ → α} {a : α}

/-- If the distance between consecutive points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
theorem cauchySeq_of_dist_le_of_summable (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) : CauchySeq f := by
  -- Porting note (#11215): TODO: with `Topology/Instances/NNReal` we can use this:
  -- lift d to ℕ → ℝ≥0 using fun n ↦ dist_nonneg.trans (hf n)
  -- refine cauchySeq_of_edist_le_of_summable d ?_ ?_
  -- · exact_mod_cast hf
  -- · exact_mod_cast hd
  refine' Metric.cauchySeq_iff'.2 fun ε εpos ↦ _
  replace hd : CauchySeq fun n : ℕ ↦ ∑ x in range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchySeq
  refine' (Metric.cauchySeq_iff'.1 hd ε εpos).imp fun N hN n hn ↦ _
  have hsum := hN n hn
  rw [Real.dist_eq, ← sum_Ico_eq_sub _ hn] at hsum
  calc
    dist (f n) (f N) = dist (f N) (f n) := dist_comm _ _
    _ ≤ ∑ x in Ico N n, d x := dist_le_Ico_sum_of_dist_le hn fun _ _ ↦ hf _
    _ ≤ |∑ x in Ico N n, d x| := le_abs_self _
    _ < ε := hsum
#align cauchy_seq_of_dist_le_of_summable cauchySeq_of_dist_le_of_summable

theorem cauchySeq_of_summable_dist (h : Summable fun n ↦ dist (f n) (f n.succ)) : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ (fun _ ↦ le_rfl) h
#align cauchy_seq_of_summable_dist cauchySeq_of_summable_dist

theorem dist_le_tsum_of_dist_le_of_tendsto (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ ∑' m, d (n + m) := by
  refine' le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_atTop.2 ⟨n, fun m hnm ↦ _⟩)
  refine' le_trans (dist_le_Ico_sum_of_dist_le hnm fun _ _ ↦ hf _) _
  rw [sum_Ico_eq_sum_range]
  refine' sum_le_tsum (range _) (fun _ _ ↦ le_trans dist_nonneg (hf _)) _
  exact hd.comp_injective (add_right_injective n)
#align dist_le_tsum_of_dist_le_of_tendsto dist_le_tsum_of_dist_le_of_tendsto

theorem dist_le_tsum_of_dist_le_of_tendsto₀ (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ tsum d := by
  simpa only [zero_add] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0
#align dist_le_tsum_of_dist_le_of_tendsto₀ dist_le_tsum_of_dist_le_of_tendsto₀

theorem dist_le_tsum_dist_of_tendsto (h : Summable fun n ↦ dist (f n) (f n.succ))
    (ha : Tendsto f atTop (𝓝 a)) (n) : dist (f n) a ≤ ∑' m, dist (f (n + m)) (f (n + m).succ) :=
  show dist (f n) a ≤ ∑' m, (fun x ↦ dist (f x) (f x.succ)) (n + m) from
    dist_le_tsum_of_dist_le_of_tendsto (fun n ↦ dist (f n) (f n.succ)) (fun _ ↦ le_rfl) h ha n
#align dist_le_tsum_dist_of_tendsto dist_le_tsum_dist_of_tendsto

theorem dist_le_tsum_dist_of_tendsto₀ (h : Summable fun n ↦ dist (f n) (f n.succ))
    (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ ∑' n, dist (f n) (f n.succ) := by
  simpa only [zero_add] using dist_le_tsum_dist_of_tendsto h ha 0
#align dist_le_tsum_dist_of_tendsto₀ dist_le_tsum_dist_of_tendsto₀
