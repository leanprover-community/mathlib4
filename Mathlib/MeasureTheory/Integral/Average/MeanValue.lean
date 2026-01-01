/-
Copyright (c) 2025 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Mean value theorem for set averages

We prove a "mean value" property for set averages.

## Main results

* `exists_eq_setAverage`: `∃ c ∈ s, f c = ⨍ x in s, f x ∂μ`.

## Notation

`⨍ x in s, f x ∂μ` is notation for `average (μ.restrict s) f`, the average value of `f` over `s`
w.r.t. `μ`.

## Tags

set average, average value, mean value
-/

@[expose] public section

open MeasureTheory

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  {s : Set α} {f : α → ℝ} {μ : Measure α}

/-- If `s` is a connected set of finite, nonzero `μ`-measure and `f : α → ℝ` is continuous on `s`
and integrable on `s` w.r.t. `μ`, then `f` attains its `μ`-average on `s`. -/
theorem exists_eq_setAverage
    (hs : IsConnected s)
    (hf : ContinuousOn f s)
    (hint : IntegrableOn f s μ)
    (hμfin : μ s ≠ ⊤)
    (hμ0 : μ s ≠ 0) :
    ∃ c ∈ s, f c = ⨍ x in s, f x ∂μ := by
  let ave := ⨍ x in s, f x ∂μ
  let S₁ : Set α := {x | x ∈ s ∧ f x ≤ ave}
  let S₂ : Set α := {x | x ∈ s ∧ ave ≤ f x}
  have hS₁ : 0 < μ S₁ := measure_le_setAverage_pos hμ0 hμfin hint
  have hS₂ : 0 < μ S₂ := measure_setAverage_le_pos hμ0 hμfin hint
  rcases nonempty_of_measure_ne_zero hS₁.ne' with ⟨c₁, hc₁⟩
  rcases nonempty_of_measure_ne_zero hS₂.ne' with ⟨c₂, hc₂⟩
  apply hs.isPreconnected.intermediate_value hc₁.1 hc₂.1 hf
  grind
