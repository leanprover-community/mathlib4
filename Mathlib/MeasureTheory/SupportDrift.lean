import Mathlib

open MeasureTheory

/--
`supportDrift μ` is the support of a probability measure viewed as a set.

This is a minimal, mathlib-facing definition intended for future
stability/continuity extensions.
-/
def supportDrift {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  (μ : MeasureTheory.ProbabilityMeasure α) : Set α :=
μ.toMeasure.support

@[simp]
lemma supportDrift_def {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  (μ : MeasureTheory.ProbabilityMeasure α) :
  supportDrift μ = μ.toMeasure.support := rfl
