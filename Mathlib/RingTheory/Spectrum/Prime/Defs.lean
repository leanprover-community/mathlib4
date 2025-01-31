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

/-- The prime spectrum of a commutative (semi)ring `R` is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `Mathlib.AlgebraicGeometry.StructureSheaf`).
It is a fundamental building block in algebraic geometry. -/
@[ext]
structure PrimeSpectrum (R : Type*) [CommSemiring R] where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime

attribute [instance] PrimeSpectrum.isPrime
