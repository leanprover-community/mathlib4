/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.FreeAlgebra

#align_import algebra.char_p.algebra from "leanprover-community/mathlib"@"96782a2d6dcded92116d8ac9ae48efb41d46a27c"

/-!
# Characteristics of algebras

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of free algebras over `R`
and the fraction field `FractionRing R`.


## Main results

- `charP_of_injective_algebraMap` If `R →+* A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances constructed from this result:
- Any `FreeAlgebra R X` has the same characteristic as `R`.
- The `FractionRing R` of an integral domain `R` has the same characteristic as `R`.

-/


/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
theorem charP_of_injective_algebraMap {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : ℕ) [CharP R p] : CharP A p :=
  { cast_eq_zero_iff' := fun x => by
      rw [← CharP.cast_eq_zero_iff R p x]
      change algebraMap ℕ A x = 0 ↔ algebraMap ℕ R x = 0
      rw [IsScalarTower.algebraMap_apply ℕ R A x]
      refine' Iff.trans _ h.eq_iff
      rw [RingHom.map_zero] }
#align char_p_of_injective_algebra_map charP_of_injective_algebraMap

theorem charP_of_injective_algebraMap' (R A : Type*) [Field R] [Semiring A] [Algebra R A]
    [Nontrivial A] (p : ℕ) [CharP R p] : CharP A p :=
  charP_of_injective_algebraMap (algebraMap R A).injective p
#align char_p_of_injective_algebra_map' charP_of_injective_algebraMap'

/-- If the algebra map `R →+* A` is injective and `R` has characteristic zero then so does `A`. -/
theorem charZero_of_injective_algebraMap {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A :=
  { cast_injective := fun x y hxy => by
      change algebraMap ℕ A x = algebraMap ℕ A y at hxy
      rw [IsScalarTower.algebraMap_apply ℕ R A x] at hxy
      rw [IsScalarTower.algebraMap_apply ℕ R A y] at hxy
      exact CharZero.cast_injective (h hxy) }
#align char_zero_of_injective_algebra_map charZero_of_injective_algebraMap

/-!
As an application, a `ℚ`-algebra has characteristic zero.
-/


-- `CharP.charP_to_charZero A _ (charP_of_injective_algebraMap h 0)` does not work
-- here as it would require `Ring A`.
section QAlgebra

variable (R : Type*) [Nontrivial R]

/-- A nontrivial `ℚ`-algebra has `CharP` equal to zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `algebraRat`. It's probably easier to go the other way: prove `CharZero R` and
automatically receive an `Algebra ℚ R` instance.
-/
theorem algebraRat.charP_zero [Semiring R] [Algebra ℚ R] : CharP R 0 :=
  charP_of_injective_algebraMap (algebraMap ℚ R).injective 0
#align algebra_rat.char_p_zero algebraRat.charP_zero

/-- A nontrivial `ℚ`-algebra has characteristic zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `algebraRat`. It's probably easier to go the other way: prove `CharZero R` and
automatically receive an `Algebra ℚ R` instance.
-/
theorem algebraRat.charZero [Ring R] [Algebra ℚ R] : CharZero R :=
  @CharP.charP_to_charZero R _ (algebraRat.charP_zero R)
#align algebra_rat.char_zero algebraRat.charZero

end QAlgebra

/-!
An algebra over a field has the same characteristic as the field.
-/


section

variable (K L : Type*) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

theorem Algebra.charP_iff (p : ℕ) : CharP K p ↔ CharP L p :=
  (algebraMap K L).charP_iff_charP p
#align algebra.char_p_iff Algebra.charP_iff

theorem Algebra.ringChar_eq : ringChar K = ringChar L := by
  rw [ringChar.eq_iff, Algebra.charP_iff K L]
  apply ringChar.charP
#align algebra.ring_char_eq Algebra.ringChar_eq

end

namespace FreeAlgebra

variable {R X : Type*} [CommSemiring R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `FreeAlgebra R X`. -/
instance charP [CharP R p] : CharP (FreeAlgebra R X) p :=
  charP_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective p
#align free_algebra.char_p FreeAlgebra.charP

/-- If `R` has characteristic `0`, then so does `FreeAlgebra R X`. -/
instance charZero [CharZero R] : CharZero (FreeAlgebra R X) :=
  charZero_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective
#align free_algebra.char_zero FreeAlgebra.charZero

end FreeAlgebra

namespace IsFractionRing

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

/-- If `R` has characteristic `p`, then so does Frac(R). -/
theorem charP_of_isFractionRing [CharP R p] : CharP K p :=
  charP_of_injective_algebraMap (IsFractionRing.injective R K) p
#align is_fraction_ring.char_p_of_is_fraction_ring IsFractionRing.charP_of_isFractionRing

/-- If `R` has characteristic `0`, then so does Frac(R). -/
theorem charZero_of_isFractionRing [CharZero R] : CharZero K :=
  @CharP.charP_to_charZero K _ (charP_of_isFractionRing R 0)
#align is_fraction_ring.char_zero_of_is_fraction_ring IsFractionRing.charZero_of_isFractionRing

variable [IsDomain R]

/-- If `R` has characteristic `p`, then so does `FractionRing R`. -/
instance charP [CharP R p] : CharP (FractionRing R) p :=
  charP_of_isFractionRing R p
#align is_fraction_ring.char_p IsFractionRing.charP

/-- If `R` has characteristic `0`, then so does `FractionRing R`. -/
instance charZero [CharZero R] : CharZero (FractionRing R) :=
  charZero_of_isFractionRing R
#align is_fraction_ring.char_zero IsFractionRing.charZero

end IsFractionRing
