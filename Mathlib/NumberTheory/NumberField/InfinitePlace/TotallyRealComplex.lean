/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Totally real and totally complex number fields

This file defines the type of totally real and totally complex number fields.

## Main Definitions and Results

* `NumberField.IsTotallyReal`: a number field `K` is totally real if all of its infinite places
  are real. In other words, the image of every ring homomorphism `K → ℂ` is a subset of `ℝ`.
* `NumberField.IsTotallyComplex`: a number field `K` is totally complex if all of its infinite
  places are complex.

## Tags

number field, infinite places, totally real, totally complex
-/

namespace NumberField

open InfinitePlace Module

section TotallyRealField

/-

## Totally real number fields

-/

/-- A number field `K` is totally real if all of its infinite places
are real. In other words, the image of every ring homomorphism `K → ℂ`
is a subset of `ℝ`. -/
@[mk_iff] class IsTotallyReal (K : Type*) [Field K] [NumberField K] where
  isReal : ∀ v : InfinitePlace K, v.IsReal

variable {K : Type*} [Field K] [NumberField K]

theorem nrComplexPlaces_eq_zero_iff :
    nrComplexPlaces K = 0 ↔ IsTotallyReal K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyReal_iff]

variable (K)

@[simp]
theorem IsTotallyReal.nrComplexPlaces_eq_zero [h : IsTotallyReal K] :
    nrComplexPlaces K = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr h

protected theorem IsTotallyReal.finrank [h : IsTotallyReal K] :
    finrank ℚ K = nrRealPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, nrComplexPlaces_eq_zero_iff.mpr h, mul_zero, add_zero]

instance : IsTotallyReal ℚ where
  isReal v := by
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact Rat.isReal_infinitePlace

end TotallyRealField

section TotallyComplexField

/-
## Totally complex number fields
-/

open InfinitePlace

/--
A number field `K` is totally complex if all of its infinite places are complex.
-/
@[mk_iff] class IsTotallyComplex (K : Type*) [Field K] [NumberField K] where
  isComplex : ∀ v : InfinitePlace K, v.IsComplex

variable {K : Type*} [Field K] [NumberField K]

theorem nrRealPlaces_eq_zero_iff :
    nrRealPlaces K = 0 ↔ IsTotallyComplex K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyComplex_iff]

variable (K)

@[simp]
theorem IsTotallyComplex.nrRealPlaces_eq_zero [h : IsTotallyComplex K] :
    nrRealPlaces K = 0 :=
  nrRealPlaces_eq_zero_iff.mpr h

protected theorem IsTotallyComplex.finrank [h : IsTotallyComplex K] :
    finrank ℚ K = 2 * nrComplexPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, nrRealPlaces_eq_zero_iff.mpr h, zero_add]

end TotallyComplexField

end NumberField
