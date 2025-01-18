/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
import Mathlib.RingTheory.Ideal.Prime

/-!
# Prime spectrum of a commutative (semi)ring as a type

The prime spectrum of a commutative (semi)ring is the type of all prime ideals.

For the Zariski topology, see `Mathlib.RingTheory.Spectrum.Prime.Topology`.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `AlgebraicGeometry.StructureSheaf`.)

## Main definitions

* `PrimeSpectrum R`: The prime spectrum of a commutative (semi)ring `R`,
  i.e., the set of all prime ideals of `R`.
-/

variable (R : Type*) [CommSemiring R]

/-- The prime spectrum of a commutative (semi)ring `R` is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `Mathlib.AlgebraicGeometry.StructureSheaf`).
It is a fundamental building block in algebraic geometry. -/
@[ext]
structure PrimeSpectrum where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime

@[deprecated (since := "2024-06-22")] alias PrimeSpectrum.IsPrime := PrimeSpectrum.isPrime

namespace PrimeSpectrum

attribute [instance] isPrime

/-- The prime spectrum is in bijection with the set of prime ideals. -/
@[simps]
def equivSubtype : PrimeSpectrum R ≃ {I : Ideal R // I.IsPrime} where
  toFun I := ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem asIdeal_range_eq : Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime} :=
  Set.ext fun J ↦
    ⟨fun hJ ↦ let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_setOf.mpr <| hj ▸ j.isPrime,
      fun hJ ↦ Set.mem_range.mpr ⟨⟨J, Set.mem_setOf.mp hJ⟩, rfl⟩⟩

end PrimeSpectrum
