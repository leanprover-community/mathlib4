/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

#align_import measure_theory.covering.one_dim from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Covering theorems for Lebesgue measure in one dimension

We have a general theory of covering theorems for doubling measures, developed notably
in `DensityTheorem.lean`. In this file, we expand the API for this theory in one dimension,
by showing that intervals belong to the relevant Vitali family.
-/


open Set MeasureTheory IsUnifLocDoublingMeasure Filter

open scoped Topology

namespace Real

theorem Icc_mem_vitaliFamily_at_right {x y : ℝ} (hxy : x < y) :
    Icc x y ∈ (vitaliFamily (volume : Measure ℝ) 1).setsAt x := by
  rw [Icc_eq_closedBall]
  -- ⊢ Metric.closedBall ((x + y) / 2) ((y - x) / 2) ∈ VitaliFamily.setsAt (vitaliF …
  refine' closedBall_mem_vitaliFamily_of_dist_le_mul _ _ (by linarith)
  -- ⊢ dist x ((x + y) / 2) ≤ 1 * ((y - x) / 2)
  rw [dist_comm, Real.dist_eq, abs_of_nonneg] <;> linarith
  -- ⊢ (x + y) / 2 - x ≤ 1 * ((y - x) / 2)
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align real.Icc_mem_vitali_family_at_right Real.Icc_mem_vitaliFamily_at_right

theorem tendsto_Icc_vitaliFamily_right (x : ℝ) :
    Tendsto (fun y => Icc x y) (𝓝[>] x) ((vitaliFamily (volume : Measure ℝ) 1).filterAt x) := by
  refine' (VitaliFamily.tendsto_filterAt_iff _).2 ⟨_, _⟩
  -- ⊢ ∀ᶠ (i : ℝ) in 𝓝[Ioi x] x, Icc x i ∈ VitaliFamily.setsAt (vitaliFamily volume …
  · filter_upwards [self_mem_nhdsWithin] with y hy using Icc_mem_vitaliFamily_at_right hy
    -- 🎉 no goals
  · intro ε εpos
    -- ⊢ ∀ᶠ (i : ℝ) in 𝓝[Ioi x] x, Icc x i ⊆ Metric.closedBall x ε
    have : x ∈ Ico x (x + ε) := ⟨le_refl _, by linarith⟩
    -- ⊢ ∀ᶠ (i : ℝ) in 𝓝[Ioi x] x, Icc x i ⊆ Metric.closedBall x ε
    filter_upwards [Icc_mem_nhdsWithin_Ioi this] with y hy
    -- ⊢ Icc x y ⊆ Metric.closedBall x ε
    rw [closedBall_eq_Icc]
    -- ⊢ Icc x y ⊆ Icc (x - ε) (x + ε)
    exact Icc_subset_Icc (by linarith) hy.2
    -- 🎉 no goals
#align real.tendsto_Icc_vitali_family_right Real.tendsto_Icc_vitaliFamily_right

theorem Icc_mem_vitaliFamily_at_left {x y : ℝ} (hxy : x < y) :
    Icc x y ∈ (vitaliFamily (volume : Measure ℝ) 1).setsAt y := by
  rw [Icc_eq_closedBall]
  -- ⊢ Metric.closedBall ((x + y) / 2) ((y - x) / 2) ∈ VitaliFamily.setsAt (vitaliF …
  refine' closedBall_mem_vitaliFamily_of_dist_le_mul _ _ (by linarith)
  -- ⊢ dist y ((x + y) / 2) ≤ 1 * ((y - x) / 2)
  rw [Real.dist_eq, abs_of_nonneg] <;> linarith
  -- ⊢ y - (x + y) / 2 ≤ 1 * ((y - x) / 2)
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align real.Icc_mem_vitali_family_at_left Real.Icc_mem_vitaliFamily_at_left

theorem tendsto_Icc_vitaliFamily_left (x : ℝ) :
    Tendsto (fun y => Icc y x) (𝓝[<] x) ((vitaliFamily (volume : Measure ℝ) 1).filterAt x) := by
  refine' (VitaliFamily.tendsto_filterAt_iff _).2 ⟨_, _⟩
  -- ⊢ ∀ᶠ (i : ℝ) in 𝓝[Iio x] x, Icc i x ∈ VitaliFamily.setsAt (vitaliFamily volume …
  · filter_upwards [self_mem_nhdsWithin] with y hy using Icc_mem_vitaliFamily_at_left hy
    -- 🎉 no goals
  · intro ε εpos
    -- ⊢ ∀ᶠ (i : ℝ) in 𝓝[Iio x] x, Icc i x ⊆ Metric.closedBall x ε
    have : x ∈ Ioc (x - ε) x := ⟨by linarith, le_refl _⟩
    -- ⊢ ∀ᶠ (i : ℝ) in 𝓝[Iio x] x, Icc i x ⊆ Metric.closedBall x ε
    filter_upwards [Icc_mem_nhdsWithin_Iio this] with y hy
    -- ⊢ Icc y x ⊆ Metric.closedBall x ε
    rw [closedBall_eq_Icc]
    -- ⊢ Icc y x ⊆ Icc (x - ε) (x + ε)
    exact Icc_subset_Icc hy.1 (by linarith)
    -- 🎉 no goals
#align real.tendsto_Icc_vitali_family_left Real.tendsto_Icc_vitaliFamily_left

end Real
