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

variable (R : Type*) [CommSemiring R]

/-- The maximal spectrum of a commutative (semi)ring `R` is the type of all
maximal ideals of `R`. -/
@[ext]
structure MaximalSpectrum where
  asIdeal : Ideal R
  isMaximal : asIdeal.IsMaximal

@[deprecated (since := "2025-01-16")] alias MaximalSpectrum.IsMaximal := MaximalSpectrum.isMaximal

namespace MaximalSpectrum

attribute [instance] isMaximal

/-- The prime spectrum is in bijection with the set of prime ideals. -/
@[simps]
def equivSubtype : MaximalSpectrum R ≃ {I : Ideal R // I.IsMaximal} where
  toFun I := ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem asIdeal_range_eq : Set.range MaximalSpectrum.asIdeal = {J : Ideal R | J.IsMaximal} :=
  Set.ext fun J ↦
    ⟨fun hJ ↦ let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_setOf.mpr <| hj ▸ j.isMaximal,
      fun hJ ↦ Set.mem_range.mpr ⟨⟨J, Set.mem_setOf.mp hJ⟩, rfl⟩⟩

end MaximalSpectrum
