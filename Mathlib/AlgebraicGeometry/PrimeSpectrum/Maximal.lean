/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.MaximalSpectrum

#align_import algebraic_geometry.prime_spectrum.maximal from "leanprover-community/mathlib"@"052f6013363326d50cb99c6939814a4b8eb7b301"

/-!
# Maximal spectrum of a commutative ring

The maximal spectrum of a commutative ring is the type of all maximal ideals.
It is naturally a subset of the prime spectrum endowed with the subspace topology.

## Main definitions

* `MaximalSpectrum R`: The maximal spectrum of a commutative ring `R`,
  i.e., the set of all maximal ideals of `R`.

## Implementation notes

The Zariski topology on the maximal spectrum is defined as the subspace topology induced by the
natural inclusion into the prime spectrum to avoid API duplication for zero loci.
-/


noncomputable section

open scoped Classical

universe u v

variable (R : Type u) [CommRing R]

variable {R}

namespace MaximalSpectrum

open PrimeSpectrum Set

theorem toPrimeSpectrum_range :
    Set.range (@toPrimeSpectrum R _) = { x | IsClosed ({x} : Set <| PrimeSpectrum R) } := by
  simp only [isClosed_singleton_iff_isMaximal]
  ext ⟨x, _⟩
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.IsMaximal, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
#align maximal_spectrum.to_prime_spectrum_range MaximalSpectrum.toPrimeSpectrum_range

/-- The Zariski topology on the maximal spectrum of a commutative ring is defined as the subspace
topology induced by the natural inclusion into the prime spectrum. -/
instance zariskiTopology : TopologicalSpace <| MaximalSpectrum R :=
  PrimeSpectrum.zariskiTopology.induced toPrimeSpectrum
#align maximal_spectrum.zariski_topology MaximalSpectrum.zariskiTopology

instance : T1Space <| MaximalSpectrum R :=
  ⟨fun x => isClosed_induced_iff.mpr
    ⟨{toPrimeSpectrum x}, (isClosed_singleton_iff_isMaximal _).mpr x.IsMaximal, by
      simpa only [← image_singleton] using preimage_image_eq {x} toPrimeSpectrum_injective⟩⟩

theorem toPrimeSpectrum_continuous : Continuous <| @toPrimeSpectrum R _ :=
  continuous_induced_dom
#align maximal_spectrum.to_prime_spectrum_continuous MaximalSpectrum.toPrimeSpectrum_continuous

end MaximalSpectrum
