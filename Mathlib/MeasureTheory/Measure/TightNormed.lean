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

* `isTightMeasureSet_iff_tendsto_measure_norm_gt`: a set of measures `S` is tight if and only if
  the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity.

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
  refine hS.comp ?_
  simp only [tendsto_smallSets_iff, mem_cocompact, eventually_atTop, ge_iff_le, forall_exists_index,
    and_imp]
  intro s t ht_compact hts
  rcases Set.eq_empty_or_nonempty t with rfl | ht_nonempty
  · simp only [Set.compl_empty, Set.univ_subset_iff] at hts
    simp [hts]
  obtain ⟨r, h_subset⟩ : ∃ r, t ⊆ {x | ‖x‖ ≤ r} := by
    obtain ⟨xmax, _, hxmax⟩ : ∃ x ∈ t, IsMaxOn (fun x ↦ ‖x‖) t x :=
      ht_compact.exists_isMaxOn (f := fun x : E ↦ ‖x‖) ht_nonempty (by fun_prop)
    exact ⟨‖xmax‖, fun x hxK ↦ hxmax hxK⟩
  refine ⟨r, fun u hu ↦ subset_trans ?_ hts⟩
  simp_rw [← not_le]
  refine Set.compl_subset_compl.mp ?_
  simp only [compl_compl, not_le]
  refine h_subset.trans fun x ↦ ?_
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  exact fun hx ↦ hx.trans hu

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

lemma isTightMeasureSet_iff_tendsto_measure_norm_gt :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) :=
  ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

end FiniteDimensional

end NormedSpace

end MeasureTheory
