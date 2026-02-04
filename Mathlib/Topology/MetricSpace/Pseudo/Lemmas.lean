/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.UniformSpace.Compact

/-!
# Extra lemmas about pseudo-metric spaces
-/

@[expose] public section

open Bornology Filter Metric Set
open scoped NNReal Topology

variable {ι α : Type*} [PseudoMetricSpace α]

instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

lemma Real.singleton_eq_inter_Icc (b : ℝ) : {b} = ⋂ (r > 0), Icc (b - r) (b + r) := by
  simp [Icc_eq_closedBall, biInter_basis_nhds Metric.nhds_basis_closedBall]

/-- Special case of the sandwich lemma; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
lemma squeeze_zero' {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ᶠ t in t₀, 0 ≤ f t)
    (hft : ∀ᶠ t in t₀, f t ≤ g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

/-- Special case of the sandwich lemma; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
lemma squeeze_zero {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall hf) (Eventually.of_forall hft) g0

/-- If `u` is a neighborhood of `x`, then for small enough `r`, the closed ball
`Metric.closedBall x r` is contained in `u`. -/
lemma eventually_closedBall_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : ℝ), closedBall x r ⊆ u := by
  obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ closedBall x ε ⊆ u := nhds_basis_closedBall.mem_iff.1 hu
  have : Iic ε ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds εpos
  filter_upwards [this] with _ hr using Subset.trans (closedBall_subset_closedBall hr) hε

lemma tendsto_closedBall_smallSets (x : α) : Tendsto (closedBall x) (𝓝 0) (𝓝 x).smallSets :=
  tendsto_smallSets_iff.2 fun _ ↦ eventually_closedBall_subset

/-- If `u` is a neighborhood of `x`, then for small enough `r`, the open ball
`Metric.ball x r` is contained in `u`. -/
lemma eventually_ball_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) : ∀ᶠ r in 𝓝 (0 : ℝ), ball x r ⊆ u :=
  (eventually_closedBall_subset hu).mono fun _r hr ↦ ball_subset_closedBall.trans hr

namespace Metric
variable {x y z : α} {ε ε₁ ε₂ : ℝ} {s : Set α}

lemma isClosed_closedBall : IsClosed (closedBall x ε) := isClosed_le (by fun_prop) continuous_const

lemma isClosed_sphere : IsClosed (sphere x ε) := isClosed_eq (by fun_prop) continuous_const

@[simp]
lemma closure_closedBall : closure (closedBall x ε) = closedBall x ε :=
  isClosed_closedBall.closure_eq

@[simp]
lemma closure_sphere : closure (sphere x ε) = sphere x ε :=
  isClosed_sphere.closure_eq

lemma closure_ball_subset_closedBall : closure (ball x ε) ⊆ closedBall x ε :=
  closure_minimal ball_subset_closedBall isClosed_closedBall

lemma frontier_ball_subset_sphere : frontier (ball x ε) ⊆ sphere x ε :=
  frontier_lt_subset_eq (by fun_prop) continuous_const

lemma frontier_closedBall_subset_sphere : frontier (closedBall x ε) ⊆ sphere x ε :=
  frontier_le_subset_eq (by fun_prop) continuous_const

lemma closedBall_zero' (x : α) : closedBall x 0 = closure {x} :=
  Subset.antisymm
    (fun _y hy =>
      mem_closure_iff.2 fun _ε ε0 => ⟨x, mem_singleton x, (mem_closedBall.1 hy).trans_lt ε0⟩)
    (closure_minimal (singleton_subset_iff.2 (dist_self x).le) isClosed_closedBall)

lemma eventually_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompact (closedBall x r) := by
  rcases exists_compact_mem_nhds x with ⟨s, s_compact, hs⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_closedBall hr

lemma exists_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∃ r, 0 < r ∧ IsCompact (closedBall x r) := by
  have : ∀ᶠ r in 𝓝[>] 0, IsCompact (closedBall x r) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_isCompact_closedBall x)
  simpa only [and_comm] using (this.and self_mem_nhdsWithin).exists

theorem biInter_gt_closedBall (x : α) (r : ℝ) : ⋂ r' > r, closedBall x r' = closedBall x r := by
  ext
  simp [forall_gt_imp_ge_iff_le_of_dense]

theorem biInter_gt_ball (x : α) (r : ℝ) : ⋂ r' > r, ball x r' = closedBall x r := by
  ext
  simp [forall_gt_iff_le]

theorem biUnion_lt_ball (x : α) (r : ℝ) : ⋃ r' < r, ball x r' = ball x r := by
  ext
  rw [← not_iff_not]
  simp [forall_lt_imp_le_iff_le_of_dense]

theorem biUnion_lt_closedBall (x : α) (r : ℝ) : ⋃ r' < r, closedBall x r' = ball x r := by
  ext
  rw [← not_iff_not]
  simp [forall_lt_iff_le]

end Metric

theorem lebesgue_number_lemma_of_metric {s : Set α} {ι : Sort*} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i := by
  simpa only [ball, UniformSpace.ball, preimage_setOf_eq, dist_comm]
    using uniformity_basis_dist.lebesgue_number_lemma hs hc₁ hc₂

theorem lebesgue_number_lemma_of_metric_sUnion {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀ c) : ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, ball x δ ⊆ t := by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂

/-- For a compact set `s` with `f` continuous at each point, there exists a uniform `δ > 0` such
that `f` has controlled variation near `s`: if `x ∈ s` and `y` is within distance `δ` of `x`,
then `f x` and `f y` are within distance `ε`. -/
theorem IsCompact.exists_forall_le_dist {β : Type*} [PseudoMetricSpace β] {s : Set α} {f : α → β}
    (hs : IsCompact s) (hf : ∀ x ∈ s, ContinuousAt f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y, dist x y < δ → dist (f x) (f y) < ε := by
  have h := fun x (hx : x ∈ s) ↦ Metric.continuousAt_iff.mp (hf x hx) (ε / 2) (half_pos hε)
  choose δₓ hδₓ h using h
  let c : s → Set α := fun ⟨x, hx⟩ ↦ ball x (δₓ x hx)
  have hcover : s ⊆ ⋃ i, c i := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hδₓ x hx)⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hs (fun _ ↦ isOpen_ball) hcover
  refine ⟨δ, hδ, fun x hx y hxy ↦ ?_⟩
  obtain ⟨⟨z, hz⟩, hball⟩ := hleb x hx
  have hxz : dist x z < δₓ z hz := hball (mem_ball_self hδ)
  have hyz : dist y z < δₓ z hz := hball (by simpa only [mem_ball, dist_comm])
  calc dist (f x) (f y)
    _ ≤ dist (f x) (f z) + dist (f y) (f z) := dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h z hz hxz) (h z hz hyz)
    _ = ε := add_halves ε
