/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Results about indicator functions, their integrals, and measures

This file has a few measure theoretic or integration-related results on indicator functions.

## Implementation notes

This file exists to avoid importing `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`
in `Mathlib.MeasureTheory.Integral.Lebesgue`.

## Todo

The result `MeasureTheory.tendsto_measure_of_tendsto_indicator` here could be proved without
integration, if we had convergence of measures results for countably generated filters. Ideally,
the present file would then become unnecessary: lemmas such as
`MeasureTheory.tendsto_measure_of_ae_tendsto_indicator` would not need integration so could be
moved out of `Mathlib.MeasureTheory.Integral.Lebesgue`, and the lemmas in this file could be
moved to, e.g., `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`.

-/

namespace MeasureTheory

section TendstoIndicator

open Filter ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {A : Set α}
variable {ι : Type*} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicators of measurable sets `Aᵢ` tend pointwise to the indicator of a set `A`
and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then the measures of `Aᵢ`
tend to the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator [NeBot L] {μ : Measure α}
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞)) L (𝓝 (A.indicator 1))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator L ?_ As_mble B_mble B_finmeas As_le_B
  · exact eventually_of_forall (by simpa only [tendsto_pi_nhds] using h_lim)
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise to
the indicator of a set `A`, then the measures `μ Aᵢ` tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure [NeBot L]
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (1 : α → ℝ≥0∞)) L (𝓝 (A.indicator 1))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L ?_ As_mble
  · exact eventually_of_forall (by simpa only [tendsto_pi_nhds] using h_lim)
  · exact measurableSet_of_tendsto_indicator L As_mble h_lim

end TendstoIndicator -- section

end MeasureTheory
