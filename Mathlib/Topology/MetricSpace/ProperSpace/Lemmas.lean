/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Proper spaces

This file contains some more involved results about `ProperSpace`s.

## Main definitions and results

* `exists_pos_lt_subset_ball`
* `exists_lt_subset_ball`
* `Metric.exists_isLocalMin_mem_ball`
-/

public section

open Set Metric

variable {α : Type*} {β : Type*} [PseudoMetricSpace α] [ProperSpace α] {x : α} {r : ℝ} {s : Set α}

/-- If a nonempty ball in a proper space includes a closed set `s`, then there exists a nonempty
ball with the same center and a strictly smaller radius that includes `s`. -/
theorem exists_pos_lt_subset_ball (hr : 0 < r) (hs : IsClosed s) (h : s ⊆ ball x r) :
    ∃ r' ∈ Ioo 0 r, s ⊆ ball x r' := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩
  have : IsCompact s :=
    (isCompact_closedBall x r).of_isClosed_subset hs (h.trans ball_subset_closedBall)
  obtain ⟨y, hys, hy⟩ : ∃ y ∈ s, s ⊆ closedBall x (dist y x) :=
    this.exists_isMaxOn (β := α) (α := ℝ) hne (by fun_prop)
  have hyr : dist y x < r := h hys
  rcases exists_between hyr with ⟨r', hyr', hrr'⟩
  exact ⟨r', ⟨dist_nonneg.trans_lt hyr', hrr'⟩, hy.trans <| closedBall_subset_ball hyr'⟩

/-- If a ball in a proper space includes a closed set `s`, then there exists a ball with the same
center and a strictly smaller radius that includes `s`. -/
theorem exists_lt_subset_ball (hs : IsClosed s) (h : s ⊆ ball x r) : ∃ r' < r, s ⊆ ball x r' := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, subset_empty_iff] at h
    subst s
    exact (exists_lt r).imp fun r' hr' => ⟨hr', empty_subset _⟩
  · exact (exists_pos_lt_subset_ball hr hs h).imp fun r' hr' => ⟨hr'.1.2, hr'.2⟩

theorem Metric.exists_isLocalMin_mem_ball [TopologicalSpace β]
    [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} {a z : α} {r : ℝ}
    (hf : ContinuousOn f (closedBall a r)) (hz : z ∈ closedBall a r)
    (hf1 : ∀ z' ∈ sphere a r, f z < f z') : ∃ z ∈ ball a r, IsLocalMin f z := by
  simp_rw [← closedBall_diff_ball] at hf1
  exact (isCompact_closedBall a r).exists_isLocalMin_mem_open ball_subset_closedBall hf hz hf1
    isOpen_ball

@[fun_prop]
lemma isProperMap_dist (x : α) : IsProperMap (dist x) :=
  isProperMap_iff_tendsto_cocompact.mpr
    ⟨by fun_prop, (tendsto_dist_left_cocompact_atTop x).trans atTop_le_cocompact⟩

omit [ProperSpace α] in
lemma properSpace_iff_isProperMap_dist : ProperSpace α ↔ ∀ x : α, IsProperMap (dist x) := by
  refine ⟨fun _ ↦ isProperMap_dist, fun H ↦ ⟨fun x r ↦ ?_⟩⟩
  convert (H x).isCompact_preimage (isCompact_closedBall 0 r)
  ext
  simp [dist_comm, Real.dist_eq]

lemma isClosedMap_dist (x : α) : IsClosedMap (dist x) := (isProperMap_dist x).isClosedMap

lemma isProperMap_nndist (x : α) : IsProperMap (nndist x) :=
  isProperMap_of_comp_of_inj (Z := ℝ) (g := (↑)) (by fun_prop) (by fun_prop)
    (isProperMap_dist x) NNReal.coe_injective

lemma isClosedMap_nndist (x : α) : IsClosedMap (nndist x) := (isProperMap_nndist _).isClosedMap
