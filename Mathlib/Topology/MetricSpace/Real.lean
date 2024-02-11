/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

import Mathlib.Data.Set.Pointwise.Interval
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Algebra.Order.Compact

/-! ## Real numbers as a pseudo-metric space

To reduce imports, this was split from `PseudoMetric.lean`.

TODO: add main results

-/

open Set Filter
open scoped Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

open Metric

section Real

/-- Instantiate the reals as a pseudometric space. -/
instance Real.pseudoMetricSpace : PseudoMetricSpace ℝ where
  dist x y := |x - y|
  dist_self := by simp [abs_zero]
  dist_comm x y := abs_sub_comm _ _
  dist_triangle x y z := abs_sub_le _ _ _
  edist_dist := fun x y => by exact ENNReal.coe_nnreal_eq _
#align real.pseudo_metric_space Real.pseudoMetricSpace

theorem Real.dist_eq (x y : ℝ) : dist x y = |x - y| := rfl
#align real.dist_eq Real.dist_eq

theorem Real.nndist_eq (x y : ℝ) : nndist x y = Real.nnabs (x - y) := rfl
#align real.nndist_eq Real.nndist_eq

theorem Real.nndist_eq' (x y : ℝ) : nndist x y = Real.nnabs (y - x) :=
  nndist_comm _ _
#align real.nndist_eq' Real.nndist_eq'

theorem Real.dist_0_eq_abs (x : ℝ) : dist x 0 = |x| := by simp [Real.dist_eq]
#align real.dist_0_eq_abs Real.dist_0_eq_abs

theorem Real.dist_left_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist x y ≤ dist x z := by
  simpa only [dist_comm x] using abs_sub_left_of_mem_uIcc h
#align real.dist_left_le_of_mem_uIcc Real.dist_left_le_of_mem_uIcc

theorem Real.dist_right_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist y z ≤ dist x z := by
  simpa only [dist_comm _ z] using abs_sub_right_of_mem_uIcc h
#align real.dist_right_le_of_mem_uIcc Real.dist_right_le_of_mem_uIcc

theorem Real.dist_le_of_mem_uIcc {x y x' y' : ℝ} (hx : x ∈ uIcc x' y') (hy : y ∈ uIcc x' y') :
    dist x y ≤ dist x' y' :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc (by rwa [uIcc_comm]) (by rwa [uIcc_comm])
#align real.dist_le_of_mem_uIcc Real.dist_le_of_mem_uIcc

theorem Real.dist_le_of_mem_Icc {x y x' y' : ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
    dist x y ≤ y' - x' := by
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 <| hx.1.trans hx.2), neg_sub] using
    Real.dist_le_of_mem_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)
#align real.dist_le_of_mem_Icc Real.dist_le_of_mem_Icc

theorem Real.dist_le_of_mem_Icc_01 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist x y ≤ 1 := by simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy
#align real.dist_le_of_mem_Icc_01 Real.dist_le_of_mem_Icc_01

instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

theorem Real.ball_eq_Ioo (x r : ℝ) : ball x r = Ioo (x - r) (x + r) :=
  Set.ext fun y => by
    rw [mem_ball, dist_comm, Real.dist_eq, abs_sub_lt_iff, mem_Ioo, ← sub_lt_iff_lt_add',
      sub_lt_comm]
#align real.ball_eq_Ioo Real.ball_eq_Ioo

theorem Real.closedBall_eq_Icc {x r : ℝ} : closedBall x r = Icc (x - r) (x + r) := by
  ext y
  rw [mem_closedBall, dist_comm, Real.dist_eq, abs_sub_le_iff, mem_Icc, ← sub_le_iff_le_add',
    sub_le_comm]
#align real.closed_ball_eq_Icc Real.closedBall_eq_Icc

theorem Real.Ioo_eq_ball (x y : ℝ) : Ioo x y = ball ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.ball_eq_Ioo, ← sub_div, add_comm, ← sub_add, add_sub_cancel', add_self_div_two,
    ← add_div, add_assoc, add_sub_cancel'_right, add_self_div_two]
#align real.Ioo_eq_ball Real.Ioo_eq_ball

theorem Real.Icc_eq_closedBall (x y : ℝ) : Icc x y = closedBall ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.closedBall_eq_Icc, ← sub_div, add_comm, ← sub_add, add_sub_cancel', add_self_div_two, ←
    add_div, add_assoc, add_sub_cancel'_right, add_self_div_two]
#align real.Icc_eq_closed_ball Real.Icc_eq_closedBall

section MetricOrdered

variable [PseudoMetricSpace α] [Preorder α] [CompactIccSpace α]

theorem totallyBounded_Icc (a b : α) : TotallyBounded (Icc a b) :=
  isCompact_Icc.totallyBounded
#align totally_bounded_Icc totallyBounded_Icc

theorem totallyBounded_Ico (a b : α) : TotallyBounded (Ico a b) :=
  totallyBounded_subset Ico_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ico totallyBounded_Ico

theorem totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a b) :=
  totallyBounded_subset Ioc_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ioc totallyBounded_Ioc

theorem totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a b) :=
  totallyBounded_subset Ioo_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ioo totallyBounded_Ioo

end MetricOrdered

variable [PseudoMetricSpace α]

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
theorem squeeze_zero' {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ᶠ t in t₀, 0 ≤ f t)
    (hft : ∀ᶠ t in t₀, f t ≤ g t) (g0 : Tendsto g t₀ (nhds 0)) : Tendsto f t₀ (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft
#align squeeze_zero' squeeze_zero'

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
theorem squeeze_zero {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (eventually_of_forall hf) (eventually_of_forall hft) g0
#align squeeze_zero squeeze_zero

theorem Metric.uniformity_eq_comap_nhds_zero :
    𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : ℝ)) := by
  ext s
  simp only [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff]
  simp [subset_def, Real.dist_0_eq_abs]
#align metric.uniformity_eq_comap_nhds_zero Metric.uniformity_eq_comap_nhds_zero

theorem cauchySeq_iff_tendsto_dist_atTop_0 [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (fun n : β × β => dist (u n.1) (u n.2)) atTop (𝓝 0) := by
  rw [cauchySeq_iff_tendsto, Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff,
    Function.comp_def]
  simp_rw [Prod_map]
#align cauchy_seq_iff_tendsto_dist_at_top_0 cauchySeq_iff_tendsto_dist_atTop_0

theorem tendsto_uniformity_iff_dist_tendsto_zero {f : ι → α × α} {p : Filter ι} :
    Tendsto f p (𝓤 α) ↔ Tendsto (fun x => dist (f x).1 (f x).2) p (𝓝 0) := by
  rw [Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff, Function.comp_def]
#align tendsto_uniformity_iff_dist_tendsto_zero tendsto_uniformity_iff_dist_tendsto_zero

theorem Filter.Tendsto.congr_dist {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
    (h₁ : Tendsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) :
    Tendsto f₂ p (𝓝 a) :=
  h₁.congr_uniformity <| tendsto_uniformity_iff_dist_tendsto_zero.2 h
#align filter.tendsto.congr_dist Filter.Tendsto.congr_dist

alias tendsto_of_tendsto_of_dist := Filter.Tendsto.congr_dist
#align tendsto_of_tendsto_of_dist tendsto_of_tendsto_of_dist

theorem tendsto_iff_of_dist {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
    (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : Tendsto f₁ p (𝓝 a) ↔ Tendsto f₂ p (𝓝 a) :=
  Uniform.tendsto_congr <| tendsto_uniformity_iff_dist_tendsto_zero.2 h
#align tendsto_iff_of_dist tendsto_iff_of_dist

/-- If `u` is a neighborhood of `x`, then for small enough `r`, the closed ball
`Metric.closedBall x r` is contained in `u`. -/
theorem eventually_closedBall_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : ℝ), closedBall x r ⊆ u := by
  obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ closedBall x ε ⊆ u := nhds_basis_closedBall.mem_iff.1 hu
  have : Iic ε ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds εpos
  filter_upwards [this] with _ hr using Subset.trans (closedBall_subset_closedBall hr) hε
#align eventually_closed_ball_subset eventually_closedBall_subset

end Real
