/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Instances.ENNReal

#align_import topology.algebra.infinite_sum.real from "leanprover-community/mathlib"@"9a59dcb7a2d06bf55da57b9030169219980660cd"

/-!
# Infinite sum in the reals

This file provides lemmas about Cauchy sequences in terms of infinite sums and infinite sums valued
in the reals.
-/

open Filter Finset NNReal Topology

variable {α β : Type*} [PseudoMetricSpace α] {f : ℕ → α} {a : α}

/-- If the distance between consecutive points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
theorem cauchySeq_of_dist_le_of_summable (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) : CauchySeq f := by
  lift d to ℕ → ℝ≥0 using fun n ↦ dist_nonneg.trans (hf n)
  apply cauchySeq_of_edist_le_of_summable d (α := α) (f := f)
  · exact_mod_cast hf
  · exact_mod_cast hd

#align cauchy_seq_of_dist_le_of_summable cauchySeq_of_dist_le_of_summable

theorem cauchySeq_of_summable_dist (h : Summable fun n ↦ dist (f n) (f n.succ)) : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ (fun _ ↦ le_rfl) h
#align cauchy_seq_of_summable_dist cauchySeq_of_summable_dist

theorem dist_le_tsum_of_dist_le_of_tendsto (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ ∑' m, d (n + m) := by
  refine le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_atTop.2 ⟨n, fun m hnm ↦ ?_⟩)
  refine le_trans (dist_le_Ico_sum_of_dist_le hnm fun _ _ ↦ hf _) ?_
  rw [sum_Ico_eq_sum_range]
  refine sum_le_tsum (range _) (fun _ _ ↦ le_trans dist_nonneg (hf _)) ?_
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

section summable

theorem not_summable_iff_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  lift f to ℕ → ℝ≥0 using hf
  exact mod_cast NNReal.not_summable_iff_tendsto_nat_atTop
#align not_summable_iff_tendsto_nat_at_top_of_nonneg not_summable_iff_tendsto_nat_atTop_of_nonneg

theorem summable_iff_not_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_atTop_of_nonneg hf]
#align summable_iff_not_tendsto_nat_at_top_of_nonneg summable_iff_not_tendsto_nat_atTop_of_nonneg

theorem summable_sigma_of_nonneg {β : α → Type*} {f : (Σ x, β x) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ := by
  lift f to (Σx, β x) → ℝ≥0 using hf
  exact mod_cast NNReal.summable_sigma
#align summable_sigma_of_nonneg summable_sigma_of_nonneg

lemma summable_partition {α β : Type*} {f : β → ℝ} (hf : 0 ≤ f) {s : α  → Set β}
    (hs : ∀ i, ∃! j, i ∈ s j) : Summable f ↔
      (∀ j, Summable fun i : s j ↦ f i) ∧ Summable fun j ↦ ∑' i : s j, f i := by
  simpa only [← (Set.sigmaEquiv s hs).summable_iff] using summable_sigma_of_nonneg (fun _ ↦ hf _)

theorem summable_prod_of_nonneg {f : (α × β) → ℝ} (hf : 0 ≤ f) :
    Summable f ↔ (∀ x, Summable fun y ↦ f (x, y)) ∧ Summable fun x ↦ ∑' y, f (x, y) :=
  (Equiv.sigmaEquivProd _ _).summable_iff.symm.trans <| summable_sigma_of_nonneg fun _ ↦ hf _

theorem summable_of_sum_le {ι : Type*} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ u : Finset ι, ∑ x ∈ u, f x ≤ c) : Summable f :=
  ⟨⨆ u : Finset ι, ∑ x ∈ u, f x,
    tendsto_atTop_ciSup (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun _ ⟨u, hu⟩ => hu ▸ h u⟩⟩
#align summable_of_sum_le summable_of_sum_le

theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : Summable f := by
  refine (summable_iff_not_tendsto_nat_atTop_of_nonneg hf).2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))
#align summable_of_sum_range_le summable_of_sum_range_le

theorem Real.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  _root_.tsum_le_of_sum_range_le (summable_of_sum_range_le hf h) h
#align real.tsum_le_of_sum_range_le Real.tsum_le_of_sum_range_le

/-- If a sequence `f` with non-negative terms is dominated by a sequence `g` with summable
series and at least one term of `f` is strictly smaller than the corresponding term in `g`,
then the series of `f` is strictly smaller than the series of `g`. -/
theorem tsum_lt_tsum_of_nonneg {i : ℕ} {f g : ℕ → ℝ} (h0 : ∀ b : ℕ, 0 ≤ f b)
    (h : ∀ b : ℕ, f b ≤ g b) (hi : f i < g i) (hg : Summable g) : ∑' n, f n < ∑' n, g n :=
  tsum_lt_tsum h hi (.of_nonneg_of_le h0 h hg) hg
#align tsum_lt_tsum_of_nonneg tsum_lt_tsum_of_nonneg

end summable
