/-
Copyright (c) 2025 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
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

@[ext]
lemma MeasureTheory.Measure.ext_of_bool {π₁ π₂ : Measure Bool}
    (h_false : π₁ {false} = π₂ {false}) (h_true : π₁ {true} = π₂ {true}) : π₁ = π₂ :=
  Measure.ext_of_singleton fun a ↦ by cases a; exacts [h_false, h_true]

@[simp]
lemma preimage_not_true : Bool.not ⁻¹' {true} = {false} := by ext x; simp

@[simp]
lemma preimage_not_false : Bool.not ⁻¹' {false} = {true} := by ext x; simp

@[simp]
lemma Measure.map_not_apply_true (π : Measure Bool) : π.map Bool.not {true} = π {false} := by
  rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial)]; simp

@[simp]
lemma Measure.map_not_apply_false (π : Measure Bool) : π.map Bool.not {false} = π {true} := by
  rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial)]; simp

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
lemma boolMeasure_apply_univ' (a b : ℝ≥0∞) : boolMeasure a b {false, true} = a + b := by
  simp [boolMeasure]

lemma boolMeasure_apply_univ (a b : ℝ≥0∞) : boolMeasure a b Set.univ = a + b := by simp

lemma measure_eq_boolMeasure (π : Measure Bool) : π = boolMeasure (π {false}) (π {true}) := by
  ext <;> simp

lemma boolMeasure_withDensity (π : Measure Bool) (f : Bool → ℝ≥0∞) :
    π.withDensity f = boolMeasure (f false * π {false}) (f true * π {true}) := by
  ext <;> simp [lintegral_dirac, mul_comm]

instance {x y : ℝ} : IsFiniteMeasure (boolMeasure (.ofReal x) (.ofReal y)) := ⟨by simp⟩

end BoolMeasure

end Bool
