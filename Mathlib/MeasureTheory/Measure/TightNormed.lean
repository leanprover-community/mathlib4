/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Order.CompletePartialOrder

/-!
# Tight sets of measures in normed spaces

Criteria for tightness of sets of measures in normed and inner product spaces.

## Main statements

* `isTightMeasureSet_iff_tendsto_measure_norm_gt`: in a finite dimensional real normed space,
  a set of measures `S` is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}`
  tends to `0` at infinity.

-/

open Filter

open scoped Topology

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E} {S : Set (Measure E)}

section NormedSpace

lemma tendsto_measure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) :
    Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) := by
  suffices Tendsto ((⨆ μ ∈ S, μ) ∘ (fun r ↦ {x | r < ‖x‖})) atTop (𝓝 0) by
    convert this with r
    simp
  refine hS.comp <| .mono_right ?_ <| monotone_smallSets Metric.cobounded_le_cocompact
  refine HasAntitoneBasis.tendsto_smallSets ?_
  exact ⟨Filter.atTop_basis_Ioi.cobounded_of_norm, fun _ _ hr x ↦ hr.trans_lt⟩

section FiniteDimensional

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma isTightMeasureSet_of_tendsto_measure_norm_gt
    (h : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε ↦ ?_
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨r, h⟩ := h ε hε
  refine ⟨Metric.closedBall 0 r, isCompact_closedBall 0 r, ?_⟩
  specialize h r le_rfl
  simp only [iSup_le_iff] at h
  convert h using 4 with μ hμ
  ext
  simp

/-- In a finite dimensional real normed space, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity. -/
lemma isTightMeasureSet_iff_tendsto_measure_norm_gt :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) :=
  ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

end FiniteDimensional

end NormedSpace

end MeasureTheory
