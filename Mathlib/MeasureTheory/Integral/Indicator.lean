/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Lebesgue

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

/-- If the indicators of measurable sets `Aᵢ` tend pointwise to the indicator of a set `A`
and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then the measures of `Aᵢ`
tend to the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator [NeBot L] (μ : Measure α)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞)) L (𝓝 (A.indicator 1))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator L μ ?_ As_mble B_mble B_finmeas As_le_B
  · exact eventually_of_forall (by simpa only [tendsto_pi_nhds] using h_lim)
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise to
the indicator of a set `A`, then the measures `μ Aᵢ` tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure [NeBot L]
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞)) L (𝓝 (A.indicator 1))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L μ ?_ As_mble
  · exact eventually_of_forall (by simpa only [tendsto_pi_nhds] using h_lim)
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim

end TendstoMeasureOfTendstoIndicator
