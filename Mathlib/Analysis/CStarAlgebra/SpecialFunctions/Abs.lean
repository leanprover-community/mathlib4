/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Absolute value of an operator defined via the continuous functional calculus

This file provides API for the absolute value for (CFC) and (CFCₙ), and includes the associated
basic API.

## Main declarations

## Implementation notes

None yet

## Notation

Not sure we will need this

## TODO

Not sure yet.

-/

open scoped NNReal

namespace CFC

section Nonunital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

section abs

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

lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a) : abs a - a = 2 • a⁻ := sorry

lemma abs_add_self (a : A) (ha : IsSelfAdjoint a) : abs a + a = 2 • a⁺ := sorry

end abs

end Nonunital

end CFC
