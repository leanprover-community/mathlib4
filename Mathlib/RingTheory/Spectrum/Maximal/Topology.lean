/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The Zariski topology on the maximal spectrum of a commutative (semi)ring

## Implementation notes

The Zariski topology on the maximal spectrum is defined as the subspace topology induced by the
natural inclusion into the prime spectrum to avoid API duplication for zero loci.
-/


noncomputable section

universe u v

variable (R : Type u) [CommRing R]

variable {R}

namespace MaximalSpectrum

open PrimeSpectrum Set

theorem toPrimeSpectrum_range :
    Set.range (@toPrimeSpectrum R _) = { x | IsClosed ({x} : Set <| PrimeSpectrum R) } := by
  simp only [isClosed_singleton_iff_isMaximal]
  ext ⟨x, _⟩
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.isMaximal, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- The Zariski topology on the maximal spectrum of a commutative ring is defined as the subspace
topology induced by the natural inclusion into the prime spectrum. -/
instance zariskiTopology : TopologicalSpace <| MaximalSpectrum R :=
  PrimeSpectrum.zariskiTopology.induced toPrimeSpectrum

instance : T1Space <| MaximalSpectrum R :=
  ⟨fun x => isClosed_induced_iff.mpr
    ⟨{toPrimeSpectrum x}, (isClosed_singleton_iff_isMaximal _).mpr x.isMaximal, by
      simpa only [← image_singleton] using preimage_image_eq {x} toPrimeSpectrum_injective⟩⟩

theorem toPrimeSpectrum_continuous : Continuous <| @toPrimeSpectrum R _ :=
  continuous_induced_dom

end MaximalSpectrum
