/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Maximal spectrum of a commutative (semi)ring

The maximal spectrum of a commutative (semi)ring is the type of all maximal ideals.
It is naturally a subset of the prime spectrum endowed with the subspace topology.

## Main definitions

* `MaximalSpectrum R`: The maximal spectrum of a commutative (semi)ring `R`,
  i.e., the set of all maximal ideals of `R`.
-/

/-- The maximal spectrum of a commutative (semi)ring `R` is the type of all
maximal ideals of `R`. -/
@[ext]
structure MaximalSpectrum (R : Type*) [CommSemiring R] where
  asIdeal : Ideal R
  isMaximal : asIdeal.IsMaximal

@[deprecated (since := "2025-01-16")] alias MaximalSpectrum.IsMaximal := MaximalSpectrum.isMaximal

attribute [instance] MaximalSpectrum.isMaximal
