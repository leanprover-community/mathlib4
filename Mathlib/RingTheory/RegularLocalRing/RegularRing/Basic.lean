/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!

# Definition of Regular Ring

In this file, we define regular rings as noetherian rings whose localization at every prime are
regular local rings.
(Note that regular local ring is not natrually regular ring in this definition).

## TODO
Show that regular local rings are regular under this definition.
This follows from localizations of regular local rings being regular (@Thmoas-Guan).

-/

@[expose] public section

open IsLocalRing

variable (R : Type*) [CommRing R]

/-- A noetherian ring is regular if its localization at any prime `IsRegularLocalRing`. -/
class IsRegularRing : Prop extends IsNoetherianRing R where
  isRegularLocalRing_localization : ∀ p : Ideal R, ∀ (_ : p.IsPrime),
    IsRegularLocalRing (Localization.AtPrime p)

variable {R} in
lemma isRegularRing_iff [IsNoetherianRing R] : IsRegularRing R ↔
    ∀ (p : Ideal R) (_ : p.IsPrime), IsRegularLocalRing (Localization.AtPrime p) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

variable {R} in
lemma isRegularRing_of_ringEquiv {R' : Type*} [CommRing R'] (e : R ≃+* R') [IsRegularRing R] :
    IsRegularRing R' := by
  have := isNoetherianRing_of_ringEquiv R e
  apply isRegularRing_iff.mpr (fun p' hp' ↦ ?_)
  have := isRegularRing_iff.mp ‹_› (p'.comap e) (Ideal.comap_isPrime e p')
  suffices (p'.comap e).primeCompl.map e = p'.primeCompl from
    IsRegularLocalRing.of_ringEquiv <| IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime (p'.comap e)) (Localization.AtPrime p') e this
  ext x
  simpa using ⟨fun ⟨y, hy, eq⟩ ↦ eq ▸ hy,
    fun h ↦ ⟨e.symm x, (e.apply_symm_apply x).symm ▸ h, e.apply_symm_apply x⟩⟩

instance (priority := low) [IsDomain R] [IsDedekindDomain R] : IsRegularRing R := by
  refine isRegularRing_iff.mpr (fun p hp ↦ ?_)
  by_cases eqbot : p = ⊥
  · let : Field (Localization.AtPrime p) := IsField.toField <| by
      simp [isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal, eqbot]
    infer_instance
  · have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      R eqbot (Localization.AtPrime p)
    infer_instance
