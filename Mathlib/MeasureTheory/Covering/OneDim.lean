/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Covering theorems for Lebesgue measure in one dimension

We have a general theory of covering theorems for doubling measures, developed notably
in `DensityTheorem.lean`. In this file, we expand the API for this theory in one dimension,
by showing that intervals shrinking to a point converge along the relevant Vitali family.
-/

public section


open Set MeasureTheory IsUnifLocDoublingMeasure Filter

open scoped Topology

namespace Real

theorem tendsto_Icc_vitaliFamily_right (x : ℝ) :
    Tendsto (fun y => Icc x y) (𝓝[>] x) ((vitaliFamily (volume : Measure ℝ)).filterAt x) := by
  simp only [Icc_eq_closedBall]
  refine tendsto_closedBall_filterAt volume (K := 1) _ _ ?_ ?_
  · refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      simpa using ((continuous_sub_right x).div_const 2).tendsto x
    · filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
      simpa using hy
  · filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
    rw [Metric.mem_closedBall, dist_eq, one_mul, abs_le]
    constructor <;> linarith

theorem tendsto_Icc_vitaliFamily_left (x : ℝ) :
    Tendsto (fun y => Icc y x) (𝓝[<] x) ((vitaliFamily (volume : Measure ℝ)).filterAt x) := by
  simp only [Icc_eq_closedBall]
  refine tendsto_closedBall_filterAt volume (K := 1) _ _ ?_ ?_
  · refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      simpa using ((continuous_sub_left x).div_const 2).tendsto x
    · filter_upwards [self_mem_nhdsWithin] with y (hy : y < x)
      simpa using hy
  · filter_upwards [self_mem_nhdsWithin] with y (hy : y < x)
    rw [Metric.mem_closedBall, dist_eq, one_mul, abs_le]
    constructor <;> linarith


end Real
