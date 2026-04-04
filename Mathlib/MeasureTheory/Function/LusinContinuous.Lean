/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Lusin's theorem

## Main results
-/

@[expose] public section


noncomputable section

open MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} [TopologicalSpace α] [TopologicalSpace β]
  {μ : Measure α}

theorem SimpleFunc.exists_continuous_restrict  [IsFiniteMeasure μ] {p : Set α → Prop}
    (hp : ∀ {ι} [Finite ι] {t : ι → Set α}, (∀ i : ι, p (t i)) → p (⋃ i, t i)) {ε : ℝ} (hε : 0 < ε)
    (hμ : μ.InnerRegularWRT p MeasurableSet) (f : SimpleFunc α β) :
    ∃ s, p s ∧ (μ sᶜ < EnnReal.ofReal ε) ∧ ContinuousOn f s := by
  sorry

theorem StronglyMeasurable.exists_continuous_restrict [IsFiniteMeasure μ] {p : Set α → Prop}
    (hp : ∀ {ι} [Finite ι] {t : ι → Set α}, (∀ i : ι, p (t i)) → p (⋃ i, t i)) {ε : ℝ} (hε : 0 < ε)
    (hμ : μ.InnerRegularWRT p MeasurableSet) {f : α → β} (hf : StronglyMeasurable f) :
    ∃ s, p s ∧ (μ.real sᶜ < EnnReal.ofReal ε) ∧ ContinuousOn f s := by
  obtain ⟨g, hg⟩ := hf
  choose t ht using fun n => (g n).exists_continuous_restrict hp hε hμ
  sorry

theorem NullMeasurable.exists_continuous_restrict [IsFiniteMeasure μ] {p : Set α → Prop}
    (hp : ∀ {ι} [Finite ι] {t : ι → Set α}, (∀ i : ι, p (t i)) → p (⋃ i, t i)) {ε : ℝ} (hε : 0 < ε)
    (hμ : μ.InnerRegularWRT p MeasurableSet) {f : α → β} [MeasurableSpace β]
    (hf : NullMeasurable f μ) :
    ∃ s, p s ∧ (μ sᶜ < EnnReal.ofReal ε) ∧ ContinuousOn f s := by
  sorry

end MeasureTheory
