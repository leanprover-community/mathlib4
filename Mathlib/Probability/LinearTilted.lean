/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments

/-!
# Linearly tilted measures

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open MeasureTheory Real

open scoped ENNReal InnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  {mα : MeasurableSpace E} {μ : Measure E} {t : E}

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- Exponentially tilted measure. When `x ↦ exp ⟪t, x⟫` is integrable, `μ.linTilted t` is the
probability measure with density with respect to `μ` proportional to `exp ⟪t, x⟫`.
Otherwise it is 0.
-/
noncomputable
def _root_.MeasureTheory.Measure.linTilted (μ : Measure E) (t : E) : Measure E :=
  μ.tilted (fun x ↦ ⟪t, x⟫)

/- API needed:
- zero measure
- zero E
- add measure?
- add E
- smul measure
- smul E, if exists
- order measure
- order E, if exists

- monotone function
- link to mgf / cgf

-/

instance : IsZeroOrProbabilityMeasure (μ.linTilted t) := by
  rw [Measure.linTilted]; infer_instance

@[simp]
lemma linTilted_zero_measure : (0 : Measure E).linTilted t = 0 := by simp [Measure.linTilted]

@[simp]
lemma linTilted_zero' : μ.linTilted (0 : E) = (μ Set.univ)⁻¹ • μ := by simp [Measure.linTilted]

@[simp]
lemma linTilted_zero [IsZeroOrProbabilityMeasure μ] : μ.linTilted (0 : E) = μ := by
  rw [linTilted_zero']
  cases eq_zero_or_isProbabilityMeasure μ with
  | inl h => simp [h]
  | inr h => simp [h]

end ProbabilityTheory
