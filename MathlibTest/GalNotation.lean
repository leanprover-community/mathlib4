/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ULift

/-! Tests for the notation `Gal(L/K)`. -/

universe uR uS uK uL

variable (R : Type uR) (S : Type uS) (K : Type uK) (L : Type uL)
variable [CommSemiring R] [Semiring S] [Algebra R S] [Field K] [Field L] [Algebra K L]

/-! `Gal(S/R)` should always elaborate to `S ≃ₐ[R] S`,
but `S ≃ₐ[R] S` should not pretty print as `Gal(S/R)` because `R` and `S` are not fields. -/

/-- info: S ≃ₐ[R] S : Type uS -/
#guard_msgs in
#check Gal(S/R)

/-! `Gal(L/K)` should pretty print as `Gal(L/K)` when `K` and `L` are fields. -/

/-- info: Gal(L/K) : Type uL -/
#guard_msgs in
#check Gal(L/K)

/-- info: Gal(L/K) : Type uL -/
#guard_msgs in
#check L ≃ₐ[K] L

/-! This should also work for concrete types other than variables -/

/-- info: Gal(ℚ/ℚ) : Type -/
#guard_msgs in
#check Gal(ℚ/ℚ)

/-- info: Gal(ULift.{uL, 0} ℚ/ℚ) : Type uL -/
#guard_msgs in
#check Gal(ULift.{uL} ℚ/ℚ)

/-! This should not see through `abbrev`s and pretty print `AlgEquiv`s between them as `Gal`. -/

/-- A copy of `L` for testing. -/
abbrev Copy := L

/-- info: Gal(Copy L/K) : Type uL -/
#guard_msgs in
#check Gal(Copy L/K)

/-- info: L ≃ₐ[K] Copy L : Type uL -/
#guard_msgs in
#check L ≃ₐ[K] Copy L

/-! `Gal(L/K)` should not pretty print when `pp.explicit` is set to true. -/

set_option pp.explicit true in
/--
info:
@AlgEquiv K L L (@Semifield.toCommSemiring K (@Field.toSemifield K inst✝²))
  (@DivisionSemiring.toSemiring L (@Semifield.toDivisionSemiring L (@Field.toSemifield L inst✝¹)))
  (@DivisionSemiring.toSemiring L (@Semifield.toDivisionSemiring L (@Field.toSemifield L inst✝¹))) inst✝ inst✝ : Type uL
-/
#guard_msgs in
#check Gal(L/K)
