/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Maximal spectrum of a commutative (semi)ring

Basic properties the maximal spectrum of a ring.
-/

noncomputable section

variable (R S P : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]

namespace MaximalSpectrum

/-- The prime spectrum is in bijection with the set of prime ideals. -/
@[simps]
def equivSubtype : MaximalSpectrum R ≃ {I : Ideal R // I.IsMaximal} where
  toFun I := ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩

theorem range_asIdeal : Set.range MaximalSpectrum.asIdeal = {J : Ideal R | J.IsMaximal} :=
  Set.ext fun J ↦
    ⟨fun hJ ↦ let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_setOf.mpr <| hj ▸ j.isMaximal,
      fun hJ ↦ Set.mem_range.mpr ⟨⟨J, Set.mem_setOf.mp hJ⟩, rfl⟩⟩

variable {R}

instance [Nontrivial R] : Nonempty <| MaximalSpectrum R :=
  let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI⟩⟩

/-- The natural inclusion from the maximal spectrum to the prime spectrum. -/
def toPrimeSpectrum (x : MaximalSpectrum R) : PrimeSpectrum R :=
  ⟨x.asIdeal, x.isMaximal.isPrime⟩

theorem toPrimeSpectrum_injective : (@toPrimeSpectrum R _).Injective := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simpa only [MaximalSpectrum.mk.injEq] using PrimeSpectrum.ext_iff.mp h

end MaximalSpectrum
