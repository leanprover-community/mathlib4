/-
Copyright (c) 2020 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Topology.NoetherianSpace

/-!
This file proves additional properties of the prime spectrum a ring is Noetherian.
-/


universe u v

namespace PrimeSpectrum

open TopologicalSpace

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

instance : NoetherianSpace (PrimeSpectrum R) := by
  apply ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr
  have H := ‹IsNoetherianRing R›
  rw [isNoetherianRing_iff, isNoetherian_iff_wellFounded] at H
  exact (closedsEmbedding R).dual.wellFounded H

lemma _root_.minimalPrimes.finite_of_isNoetherianRing : (minimalPrimes R).Finite :=
  minimalPrimes.equivIrreducibleComponents R
    |>.set_finite_iff
    |>.mpr NoetherianSpace.finite_irreducibleComponents

end PrimeSpectrum
