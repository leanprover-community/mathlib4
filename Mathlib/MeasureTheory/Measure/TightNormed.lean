/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Measure.RegularityCompacts
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

open scoped Topology ENNReal RealInnerProductSpace

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

section InnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma isTightMeasureSet_of_forall_basis_tendsto (b : OrthonormalBasis ι ℝ E)
    (h : ∀ i, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < |⟪b i, x⟫|}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot]
    convert tendsto_pure_nhds (a := ∅) _
    simp
  have h_rank : (0 : ℝ) < Fintype.card ι := by
    simp only [← Module.finrank_eq_card_basis b.toBasis, Nat.cast_pos, Module.finrank_pos_iff]
    infer_instance
  have : Nonempty ι := by simpa [Fintype.card_pos_iff] using h_rank
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have h_le : (fun r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖})
      ≤ fun r ↦ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
    intro r
    calc ⨆ μ ∈ S, μ {x | r < ‖x‖}
    _ ≤ ⨆ μ ∈ S, μ (⋃ i, {x : E | r / √(Fintype.card ι) < |⟪b i, x⟫|}) := by
      gcongr with μ hμS
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hx ⊢
      have hx' : r < √(Fintype.card ι) * ⨆ i, |⟪b i, x⟫| :=
        hx.trans_le (b.norm_le_card_mul_iSup_abs_inner x)
      rw [← div_lt_iff₀' (by positivity)] at hx'
      by_contra! h_le
      exact lt_irrefl (r / √(Fintype.card ι)) (hx'.trans_le (ciSup_le h_le))
    _ ≤ ⨆ μ ∈ S, ∑ i, μ {x : E | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
      gcongr with μ hμS
      exact measure_iUnion_fintype_le μ _
    _ ≤ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
      refine iSup_le fun μ ↦ (iSup_le fun hμS ↦ ?_)
      gcongr with i
      exact le_biSup (fun μ ↦ μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|}) hμS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') h_le
  rw [← Finset.sum_const_zero]
  refine tendsto_finset_sum Finset.univ fun i _ ↦ ?_
  refine (h i).comp ?_
  exact Tendsto.atTop_div_const (by positivity) tendsto_id

lemma isTightMeasureSet_iff_forall_basis_tendsto (b : OrthonormalBasis ι ℝ E) :
    IsTightMeasureSet S
      ↔ ∀ i, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < |⟪b i, x⟫|}) atTop (𝓝 0) := by
  refine ⟨fun h i ↦ ?_, isTightMeasureSet_of_forall_basis_tendsto b⟩
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le') ?_
  intro r
  have h_le (μ : Measure E) : μ {x | r < |⟪b i, x⟫|} ≤ μ {x | r < ‖x‖} := by
    refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    refine hx.trans_le ?_
    exact (abs_real_inner_le_norm _ _).trans <| by simp
  refine iSup₂_le_iff.mpr fun μ hμS ↦ ?_
  exact le_iSup_of_le (i := μ) <| by simp [hμS, h_le]

end InnerProductSpace

end NormedAddCommGroup

end MeasureTheory
