/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.Algebra.CayleyDickson

/-!
# Octonions, sedenions, and the Cayley–Dickson tower over the quaternions

The octonions are the Cayley–Dickson double of the quaternions, the sedenions the double
of the octonions. Both are *not associative* (`NonAssocRing`); the sedenions are not even
alternative and have zero divisors. All the structure comes from the generic construction
in `Mathlib/Algebra/CayleyDickson.lean`; this file only fixes the base of the tower by
providing the `StarModule` instance for the quaternions.

## Main definitions

* `Octonion R`: the octonions over `R`.
* `Sedenion R`: the sedenions over `R`.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. 39 (2002)

-/

@[expose] public section

open Quaternion

/-- Scalars with a trivial star act star-equivariantly on the quaternions. -/
instance Quaternion.instStarModule {R S : Type*} [CommRing R] [Monoid S]
    [DistribMulAction S R] [Star S] [TrivialStar S] : StarModule S ℍ[R] :=
  ⟨fun s a => by rw [star_trivial s, Quaternion.star_smul]⟩

/-- The octonions over a commutative ring `R`: the Cayley–Dickson double of the
quaternions. -/
abbrev Octonion (R : Type*) [CommRing R] := CayleyDickson ℍ[R]

/-- The sedenions over a commutative ring `R`: the Cayley–Dickson double of the
octonions. The sedenions are not alternative and have zero divisors, but the doubling
unit still satisfies `ℓ * (ℓ * x) = -x` (`CayleyDickson.unit_mul_unit_mul`). -/
abbrev Sedenion (R : Type*) [CommRing R] := CayleyDickson (Octonion R)

/-- The trigintaduonions (32-ons) over a commutative ring `R`. -/
abbrev Trigintaduonion (R : Type*) [CommRing R] := CayleyDickson (Sedenion R)

namespace Octonion

variable {R : Type*} [CommRing R]

example : NonAssocRing (Octonion R) := inferInstance
example : StarRing (Octonion R) := inferInstance
example : NonAssocRing (Sedenion R) := inferInstance
example : StarRing (Sedenion R) := inferInstance
example : Module.Finite R (Sedenion R) := inferInstance

end Octonion
