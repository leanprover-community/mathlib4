/-
Copyright (c) 2020 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.NoetherianSpace

/-!
This file proves additional properties of the prime spectrum a ring is Noetherian.
-/

@[expose] public section


universe u v

namespace PrimeSpectrum

open TopologicalSpace

section IsNoetherianRing

variable (R : Type u) [CommSemiring R] [IsNoetherianRing R]

instance : NoetherianSpace (PrimeSpectrum R) :=
  ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr (closedsEmbedding R).dual.wellFoundedLT

lemma finite_setOf_isMin :
    {x : PrimeSpectrum R | IsMin x}.Finite := by
  have : Function.Injective (asIdeal (R := R)) := @PrimeSpectrum.ext _ _
  refine Set.Finite.of_finite_image (f := asIdeal) ?_ this.injOn
  simp_rw [isMin_iff]
  exact (minimalPrimes.finite_of_isNoetherianRing R).subset (Set.image_preimage_subset _ _)

end IsNoetherianRing

section IsArtinianRing

variable (R : Type u) [CommRing R] [IsArtinianRing R]

instance : Ring.KrullDimLE 0 R := .mk₀ fun _ _ ↦ inferInstance

instance : DiscreteTopology (PrimeSpectrum R) :=
  discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩

variable {R} in
lemma _root_.IsArtinianRing.exists_not_mem_forall_mem_of_ne (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, IsIdempotentElem r ∧ ∀ q : Ideal R, q.IsPrime → q ≠ p → r ∈ q := by
  classical
  obtain ⟨r, hr⟩ := PrimeSpectrum.toPiLocalization_bijective.2 (Pi.single ⟨p, inferInstance⟩ 1)
  have : algebraMap R (Localization p.primeCompl) r = 1 := by
    simpa [PrimeSpectrum.toPiLocalization,
      -FaithfulSMul.algebraMap_eq_one_iff] using funext_iff.mp hr ⟨p, inferInstance⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, this]
    simp
  · apply PrimeSpectrum.toPiLocalization_bijective.injective
    simp [map_mul, hr, ← Pi.single_mul]
  · intro q hq e
    have : PrimeSpectrum.mk q inferInstance ≠ ⟨p, inferInstance⟩ := ne_of_apply_ne (·.1) e
    have : (algebraMap R (Localization.AtPrime q)) r = 0 := by
      simpa [PrimeSpectrum.toPiLocalization, this,
        -FaithfulSMul.algebraMap_eq_zero_iff] using funext_iff.mp hr ⟨q, inferInstance⟩
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, this]
    simp

end IsArtinianRing

end PrimeSpectrum
