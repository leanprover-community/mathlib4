/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Measurability of Birkhoff sums
-/

public section

open MeasureTheory

variable {α β R : Type*} [MeasurableSpace α] [AddCommMonoid β] {f : α → α} {g : α → β} {n : ℕ}
  {μ : Measure α} [DivisionSemiring R] [Module R β]

section Measurable

variable [MeasurableSpace β] [MeasurableAdd₂ β] [MeasurableConstSMul R β]

@[fun_prop]
lemma measurable_birkhoffSum (hf : Measurable f) (hg : Measurable g) :
    Measurable (birkhoffSum f g n) := by
  fun_prop [birkhoffSum]

@[fun_prop]
lemma measurable_birkhoffAverage (hf : Measurable f) (hg : Measurable g) :
    Measurable (birkhoffAverage R f g n) := by
  fun_prop [birkhoffAverage]

end Measurable

section AEStronglyMeasurable

variable [TopologicalSpace β] [ContinuousAdd β] [ContinuousConstSMul R β]

@[fun_prop]
lemma aestronglyMeasurable_birkhoffSum (hf : MeasurePreserving f μ μ)
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffSum f g n) μ := by
  apply Finset.aestronglyMeasurable_fun_sum
  exact fun i _ ↦ hg.comp_measurePreserving (hf.iterate i)

@[fun_prop]
lemma aestronglyMeasurable_birkhoffAverage (hf : MeasurePreserving f μ μ)
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffAverage R f g n) μ := by
  fun_prop [birkhoffAverage]

end AEStronglyMeasurable
