/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nilpotent.End

/-!
# Krull dimension of localization
-/

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- If `f : R →+* S` is a localization, then `ringKrullDim S ≤ ringKrullDim R`. -/
theorem ringKrullDim_le_of_isLocalization (M : Submonoid R) [Algebra R S] [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (fun I ↦ ⟨Ideal.comap (algebraMap R S) I.asIdeal, inferInstance⟩)
    (Monotone.strictMono_of_injective (fun _ _ hab ↦ Ideal.comap_mono hab)
      (fun I J h => PrimeSpectrum.ext_iff.mpr <| (by
        rw [← IsLocalization.map_comap M S I.asIdeal, ← IsLocalization.map_comap M S J.asIdeal]
        congr 1
        exact congr_arg PrimeSpectrum.asIdeal h)))

theorem ringKrullDim_localization_le_ (M : Submonoid R) :
    ringKrullDim (Localization M) ≤ ringKrullDim R :=
  ringKrullDim_le_of_isLocalization M

lemma Ring.KrullDimLE.of_isLocalization (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (n : ℕ) [Ring.KrullDimLE n R] :
    Ring.KrullDimLE n S :=
  ⟨(ringKrullDim_le_of_isLocalization M).trans Order.KrullDimLE.krullDim_le⟩

instance (M : Submonoid R) (n : ℕ) [Ring.KrullDimLE n R] :
    Ring.KrullDimLE n (Localization M) :=
  .of_isLocalization M n
