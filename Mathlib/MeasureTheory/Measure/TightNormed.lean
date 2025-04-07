/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Order.CompletePartialOrder

/-!
# Tight sets of measures in normed spaces

Criteria for tightness of sets of measures in normed and inner product spaces.

## Main statements

* `isTightMeasureSet_iff_tendsto_measure_norm_gt`: in a proper normed group, a set of measures `S`
  is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity.

-/

open Filter

open scoped Topology

namespace MeasureTheory

variable {E : Type*} {mE : MeasurableSpace E} {S : Set (Measure E)}

section PseudoMetricSpace

variable [PseudoMetricSpace E]

lemma tendsto_measure_compl_closedBall_of_isTightMeasureSet (hS : IsTightMeasureSet S) (x : E) :
    Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0) := by
  suffices Tendsto ((⨆ μ ∈ S, μ) ∘ (fun r ↦ (Metric.closedBall x r)ᶜ)) atTop (𝓝 0) by
    convert this with r
    simp
  refine hS.comp <| .mono_right ?_ <| monotone_smallSets Metric.cobounded_le_cocompact
  exact (Metric.hasAntitoneBasis_cobounded_compl_closedBall _).tendsto_smallSets

lemma isTightMeasureSet_of_tendsto_measure_compl_closedBall [ProperSpace E] {x : E}
    (h : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε ↦ ?_
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨r, h⟩ := h ε hε
  exact ⟨Metric.closedBall x r, isCompact_closedBall x r, by simpa using h r le_rfl⟩

/-- In a proper pseudo-metric space, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ` tends to `0` at infinity. -/
lemma isTightMeasureSet_iff_tendsto_measure_compl_closedBall [ProperSpace E] (x : E) :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0) :=
  ⟨fun hS ↦ tendsto_measure_compl_closedBall_of_isTightMeasureSet hS x,
    isTightMeasureSet_of_tendsto_measure_compl_closedBall⟩

end PseudoMetricSpace

section NormedAddCommGroup

variable [NormedAddCommGroup E]

lemma tendsto_measure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) :
    Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) := by
  have h := tendsto_measure_compl_closedBall_of_isTightMeasureSet hS 0
  convert h using 6 with r
  ext
  simp

lemma isTightMeasureSet_of_tendsto_measure_norm_gt [ProperSpace E]
    (h : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := 0) ?_
  convert h using 6 with r
  ext
  simp

/-- In a proper normed group, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity. -/
lemma isTightMeasureSet_iff_tendsto_measure_norm_gt [ProperSpace E] :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) :=
  ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

end NormedAddCommGroup

end MeasureTheory
