/-
Copyright (c) 2025 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# BoolMeasure

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


open MeasureTheory

open scoped ENNReal NNReal

lemma MeasureTheory.Measure.ext_of_discrete {α : Type*} {_ : MeasurableSpace α} {μ ν : Measure α}
    [Countable α] [DiscreteMeasurableSpace α] (h : ∀ a, μ {a} = ν {a}) : μ = ν := by
  ext s hs
  rw [← Set.biUnion_of_singleton s, measure_iUnion, measure_iUnion]
  · congr with i
    by_cases hi : i ∈ s
    · simp [hi, h]
    · simp [hi]
  · intro i j hij
    simp [hij.symm]
  · intro i
    by_cases hi : i ∈ s <;> simp [hi]
  · intro i j hij
    simp [hij.symm]
  · intro i
    by_cases hi : i ∈ s <;> simp [hi]

@[ext]
lemma MeasureTheory.Measure.ext_of_bool {π₁ π₂ : Measure Bool}
    (h_false : π₁ {false} = π₂ {false}) (h_true : π₁ {true} = π₂ {true}) : π₁ = π₂ := by
  refine Measure.ext_of_discrete fun a ↦ ?_
  cases a with
  | false => exact h_false
  | true => exact h_true

namespace Bool

lemma lintegral_bool {f : Bool → ℝ≥0∞} (π : Measure Bool) :
    ∫⁻ x, f x ∂π = f false * π {false} + f true * π {true} := by simp [add_comm, lintegral_fintype]

section BoolMeasure

/-- A measure on `Bool` constructed from the two values it takes on `false` and `true`. -/
noncomputable
def boolMeasure (a b : ℝ≥0∞) : Measure Bool := a • Measure.dirac false + b • Measure.dirac true

@[simp]
lemma boolMeasure_apply_false (a b : ℝ≥0∞) : boolMeasure a b {false} = a := by simp [boolMeasure]

@[simp]
lemma boolMeasure_apply_true (a b : ℝ≥0∞) : boolMeasure a b {true} = b := by simp [boolMeasure]

@[simp]
lemma boolMeasure_apply_univ (a b : ℝ≥0∞) : boolMeasure a b {false, true} = a + b := by
  simp [boolMeasure]

lemma measure_eq_boolMeasure (π : Measure Bool) : π = boolMeasure (π {false}) (π {true}) := by
  ext <;> simp

lemma boolMeasure_withDensity (π : Measure Bool) (f : Bool → ℝ≥0∞) :
    π.withDensity f = boolMeasure (f false * π {false}) (f true * π {true}) := by
  ext <;> simp [lintegral_dirac, mul_comm]

instance {x y : ℝ} : IsFiniteMeasure (boolMeasure (.ofReal x) (.ofReal y)) := ⟨by simp⟩

end BoolMeasure

end Bool
