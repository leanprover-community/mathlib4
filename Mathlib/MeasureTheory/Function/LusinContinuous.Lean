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

theorem SimpleFunc.exists_continuous_restrict {p : Set α → Prop} [IsFiniteMeasure μ]
    (hμ : μ.InnerRegularWRT p MeasurableSet) (f : SimpleFunc α β) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, p s ∧ (μ.real sᶜ < ε) ∧ ContinuousOn f s := by
  sorry

end MeasureTheory
