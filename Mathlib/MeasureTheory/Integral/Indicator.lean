/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Results about indicator functions and measures

## Main results

The section "IndicatorConstMeasurable" contains simple results showing that if the indicator
function of a set is a pointwise limit (resp. a.e.-limit) of indicators of measurable
(resp. null-measurable) sets, then the set itself is measurable (resp. null-measurable).

The section "Limits of measures of sets from limits of indicators" contains simple results showing
that the pointwise convergence of indicator functions of sets implies the convergence of measures:
limᵢ Aᵢ.indicator = A.indicator implies limᵢ μ(Aᵢ) = μ(A).

## Tags

indicator function, measure, dominated convergence of measure

-/

/-
Where should these results live? Should they be put in different files or should a new file
devoted to measure-theoretic lemmas about indicators be created?

I believe those in section IndicatorConstMeasurable only have prerequisites
 * `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`
 * `Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic`
   (for the ones using `AEStronglyMeasurable`)

Those in section TendstoMeasureOfTendstoIndicator (except to the extent they rely on measurability)
only have prerequisites
 * `Mathlib.MeasureTheory.Integral.Lebesgue`
 -/

open MeasureTheory Set Filter Topology ENNReal NNReal BigOperators

section TendstoMeasureOfTendstoIndicator
/-!
### Limits of measures of sets from limits of indicators

This section contains results showing that the pointwise convergence of indicator functions of
sets implies the convergence of measures: limᵢ Aᵢ.indicator = A.indicator implies
limᵢ μ(Aᵢ) = μ(A).
-/

variable {α : Type _} [MeasurableSpace α] {A : Set α}
variable {ι : Type _} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicators of measurable sets `Aᵢ` tend pointwise almost everywhere to the indicator
of a measurable set `A` and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then
the measures of `Aᵢ` tend to the measure of `A`. -/
lemma tendsto_measure_of_ae_tendsto_indicator (μ : Measure α) (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (fun _ ↦ (1 : ℝ≥0∞)))
          (eventually_of_forall ?_) ?_ ?_ h_lim
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    exact eventually_of_forall (fun x ↦ indicator_le_indicator_of_subset hi (by simp) x)
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas

--#find_home tendsto_measure_of_ae_tendsto_indicator
-- Gives: `Mathlib.MeasureTheory.Integral.Lebesgue`.

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise
almost everywhere to the indicator of a measurable set `A`, then the measures `μ Aᵢ` tend to
the measure `μ A`. -/
lemma tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure [IsCountablyGenerated L]
    (μ : Measure α) [IsFiniteMeasure μ] (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) :=
  tendsto_measure_of_ae_tendsto_indicator L μ A_mble As_mble MeasurableSet.univ
    (measure_ne_top μ univ) (eventually_of_forall (fun i ↦ subset_univ (As i))) h_lim

/-- If the indicators of measurable sets `Aᵢ` tend pointwise to the indicator of a set `A`
and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then the measures of `Aᵢ`
tend to the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator [NeBot L] (μ : Measure α)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator L μ ?_ As_mble B_mble B_finmeas As_le_B
  · exact eventually_of_forall (by simpa only [tendsto_pi_nhds] using h_lim)
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise to
the indicator of a set `A`, then the measures `μ Aᵢ` tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure [NeBot L]
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L μ ?_ As_mble
  · exact eventually_of_forall (by simpa only [tendsto_pi_nhds] using h_lim)
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim

end TendstoMeasureOfTendstoIndicator
