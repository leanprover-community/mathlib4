/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Translations

#align_import algebra.continued_fractions.continuants_recurrence from "leanprover-community/mathlib"@"5f11361a98ae4acd77f5c1837686f6f0102cdc25"

/-!
# Recurrence Lemmas for the `continuant` Function of Continued Fractions.

## Summary

Given a finite generalized continued fraction `f`, for all `n ≥ 1`, we prove that the `continuant`
function indeed satisfies the following recurrences:
- `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
- `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/


namespace FGCF

variable {K : Type*} (h : K) (l : List (K × K)) (p₁ p₂ : K × K) [DivisionRing K]

#noalign generalized_continued_fraction.continuants_aux_recurrence


#noalign generalized_continued_fraction.continuants_recurrence_aux

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂` and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
@[simp]
theorem continuant_recurrence  :
    continuant ⟨h, l ++ [p₁, p₂]⟩ =
      (p₂.2 * (continuant ⟨h, l ++ [p₁]⟩).1 + p₂.1 * (continuant ⟨h, l⟩).1,
        p₂.2 * (continuant ⟨h, l ++ [p₁]⟩).2 + p₂.1 * (continuant ⟨h, l⟩).2) := by
  simp [continuant]
#align generalized_continued_fraction.continuants_recurrence FGCF.continuant_recurrenceₓ

@[simp]
theorem continuant_pair  :
    continuant ⟨h, [p₁, p₂]⟩ = (p₂.2 * (p₁.2 * h + p₁.1) + p₂.1 * h, p₂.2 * p₁.2 + p₂.1) := by
  simp [continuant]

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`. -/
@[simp]
theorem numerator_recurrence :
    numerator ⟨h, l ++ [p₁, p₂]⟩ =
      p₂.2 * numerator ⟨h, l ++ [p₁]⟩ + p₂.1 * numerator ⟨h, l⟩ := by
  simp [numerator]
#align generalized_continued_fraction.numerators_recurrence FGCF.numerator_recurrenceₓ

@[simp]
theorem numerator_pair  :
    numerator ⟨h, [p₁, p₂]⟩ = p₂.2 * (p₁.2 * h + p₁.1) + p₂.1 * h := by
  simp [numerator]

/-- Shows that `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
@[simp]
theorem denominator_recurrence :
    denominator ⟨h, l ++ [p₁, p₂]⟩ =
      p₂.2 * denominator ⟨h, l ++ [p₁]⟩ + p₂.1 * denominator ⟨h, l⟩ := by
  simp [denominator]
#align generalized_continued_fraction.denominators_recurrence FGCF.denominator_recurrenceₓ

@[simp]
theorem denominator_pair  :
    denominator ⟨h, [p₁, p₂]⟩ = p₂.2 * p₁.2 + p₂.1 := by
  simp [denominator]

end FGCF
