/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow

/-!
# Absolute value of an operator defined via the continuous functional calculus

This file defines the absolute value via the (unital and nonunital) continuous functional calculus
(CFC) and (CFCₙ), and includes the associated basic API.

## Main declarations

+ `CFC.abs`: The absolute value declaration using...


## Implementation notes

None yet

## Notation

Not sure we will need this

## TODO

-/

open scoped NNReal

namespace CFC

section Nonunital

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A]
  [Module ℝ≥0 A] [SMulCommClass ℝ≥0 A A] [IsScalarTower ℝ≥0 A A]
  [NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]

section abs

/-- The absolute value of an operator, using the nonunital continuous functional calculus. -/
noncomputable def abs (a : A) := sqrt (star a * a)

@[simp]
theorem abs_nonneg {a : A} : 0 ≤ abs a := sqrt_nonneg

variable [StarOrderedRing A] [UniqueNonUnitalContinuousFunctionalCalculus NNReal A]

theorem abs_mul_self_eq_star_mul_self (a : A) : (abs a) * (abs a) = star a * a := by
  refine sqrt_mul_sqrt_self _ <| star_mul_self_nonneg _

theorem abs_sq_eq_star_mul_self (a : A) : (abs a) ^ (2 : NNReal) = star a * a := by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_self_eq_star_mul_self

variable [CStarRing A]

theorem abs_eq_zero_iff_eq_zero {a : A} : abs a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    have := congrArg (fun x ↦ x ^ (2 : NNReal)) ha
    simpa only [zero_nnrpow, abs_sq_eq_star_mul_self, CStarRing.star_mul_self_eq_zero_iff]
  · intro h
    simp only [h, abs, star_zero, mul_zero, sqrt_zero]

end abs

end Nonunital

end CFC
