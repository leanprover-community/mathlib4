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
basic API. THIS NEEDS UPDATING!

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

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0 := by
  rw [abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsSelfAdjoint.mul_self_nonneg {a : A} (ha : IsSelfAdjoint a) : 0 ≤ a * a := by
  simpa [ha.star_eq] using star_mul_self_nonneg a

-- Jireh identified this more spartan set of typeclasses for proving `sqrt_eq_cfcₙ_real_sqrt`.
-- Maybe incorporate these? From Jireh:

-- I modified these classes, these suffice to prove `sqrt_eq_cfcₙ_real_sqrt`
-- however, I think there's an issue in the library: `CFC.sqrt_eq_iff` (and probably lots around it)
-- requires `NonUnitalNormedRing`. I don't think it should and this is a mistake.

--variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A]
--   [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
--   [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
--   [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
--   [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

lemma sqrt_eq_cfcₙ_real_sqrt {a : A} (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  rw [sqrt_eq_iff _ (hb := cfcₙ_nonneg (A := A) (fun x _ ↦ Real.sqrt_nonneg x)),
    ← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id (R := ℝ) a]
  refine cfcₙ_congr fun x hx ↦ ?_
  refine Real.mul_self_sqrt ?_
  exact quasispectrum_nonneg_of_nonneg a ha x hx

lemma sq {a : A} (ha : IsSelfAdjoint a) : a * a = cfcₙ (fun (x : ℝ) ↦ x ^ 2) a := by
  sorry

lemma sqrt_silly {a : A} (ha : IsSelfAdjoint a) :
    cfcₙ Real.sqrt (a * a) = cfcₙ (fun x ↦ √(x ^ 2)) a := by
  rw [sq ha, ← cfcₙ_comp a (f := fun x ↦ x ^ 2) (g := fun x ↦ √x)]
  rfl

lemma abs_eq_cfcₙ_norm {a : A} (ha : IsSelfAdjoint a) :
    abs a = cfcₙ (‖·‖) a := by
   simp only [abs, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, sq]
   rw [sqrt_eq_cfcₙ_real_sqrt (star_mul_self_nonneg a), ha.star_eq, sqrt_silly ha]

lemma abs_eq_cfcₙ_norm_complex (a : A) [ha : IsStarNormal a] :
    abs a = cfcₙ (fun z : ℂ ↦ (‖z‖ : ℂ)) a :=
  sorry

lemma abs_of_nonneg (a : A) (ha : 0 ≤ a) : abs a = a := sorry

lemma abs_eq_posPart_add_negPart (a : A) (ha : IsSelfAdjoint a) : abs a = a⁺ + a⁻ := sorry

lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a) : abs a - a = 2 • a⁻ := sorry

lemma abs_add_self (a : A) (ha : IsSelfAdjoint a) : abs a + a = 2 • a⁺ := sorry

-- `r` of the appropriate kinds, so this is actually multiple lemmas
lemma abs_smul : abs (r • a) = |r| • abs a := sorry

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- for these you need the algebra to be unital
lemma abs_algebraMap_complex (z : ℂ) : abs (algebraMap ℂ A z) = algebraMap ℝ A |z| := sorry
lemma abs_algebraMap_real (x : ℝ) : abs (algebraMap ℝ A x) = algebraMap ℝ A |x| := sorry
lemma abs_algebraMap_nnreal (x : ℝ≥0) : abs (algebraMap ℝ≥0 A x) = algebraMap ℝ≥0 A x := sorry
lemma abs_natCast (n : ℕ) : abs (n : A) = n := sorry

end Unital

end CFC
