/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow
--import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

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

+ Need to revert this file back to the bare bones abs file, and move the stuff that uses
  the CStar instances into another file for special functions under CStarAlgebra.
-/

open scoped NNReal

namespace CFC

section Nonunital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

section abs

/-- The absolute value of an operator, using the nonunital continuous functional calculus. -/
noncomputable def abs (a : A) := sqrt (star a * a)

@[simp]
lemma abs_nonneg {a : A} : 0 ≤ abs a := sqrt_nonneg

lemma abs_mul_self_eq_star_mul_self (a : A) : (abs a) * (abs a) = star a * a := by
  refine sqrt_mul_sqrt_self _ <| star_mul_self_nonneg _

lemma abs_sq_eq_star_mul_self (a : A) : (abs a) ^ (2 : NNReal) = star a * a := by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_self_eq_star_mul_self

lemma abs_pow_eq_star_mul_self_pow (a : A) (x : ℝ≥0) :
    (abs a) ^ (2 * x) = (star a * a) ^ x := by
  sorry

/-- This and the previous need new names. -/
lemma abs_pow_eq_star_mul_self_pow_by_two (a : A) (x : ℝ≥0) :
    (abs a) ^ x = (star a * a) ^ (x / 2) := by sorry

lemma abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0 := by
  rw [abs, sqrt_eq_zero_iff _ (ha := star_mul_self_nonneg _), CStarRing.star_mul_self_eq_zero_iff]

lemma abs_eq_cfcₙ_norm (a : A) (ha : IsSelfAdjoint a) :
    abs a = cfcₙ (‖·‖) a :=
  sorry

lemma abs_eq_cfcₙ_norm_complex (a : A) [ha : IsStarNormal a] :
    abs a = cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a :=
  sorry

lemma abs_of_nonneg (a : A) (ha : 0 ≤ a) : abs a = a := sorry

lemma abs_eq_posPart_add_negPart (a : A) (ha : IsSelfAdjoint a) : abs a = a⁺ + a⁻ := sorry

lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a) : abs a - a = 2 • a⁻

lemma abs_add_self (a : A) (ha : IsSelfAdjoint a) : abs a + a = 2 • a⁺

end abs

end Nonunital

end CFC
