/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!

# Definition of Regular Ring

In this file, we define regular ring as ring with localization at every prime is regular local ring.
(Regular local ring is not natrually regular ring in this definition).

-/

@[expose] public section

open IsLocalRing

variable (R : Type*) [CommRing R]

/-- A ring is regular if its localization at any prime `IsRegularLocalRing`. -/
class IsRegularRing : Prop where
  localization_isRegular : ∀ p : Ideal R, ∀ (_ : p.IsPrime),
    IsRegularLocalRing (Localization.AtPrime p)

lemma isRegularRing_iff : IsRegularRing R ↔ ∀ p : Ideal R, ∀ (_ : p.IsPrime),
    IsRegularLocalRing (Localization.AtPrime p) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isRegularRing_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    (e : R ≃+* R') [reg : IsRegularRing R] : IsRegularRing R' := by
  apply (isRegularRing_iff R').mpr (fun p' hp' ↦ ?_)
  let p := p'.comap e
  have : Submonoid.map e.toMonoidHom p.primeCompl = p'.primeCompl := by
    ext x
    have : (∃ y, e y ∉ p' ∧ e y = x) ↔ x ∉ p' := ⟨fun ⟨y, hy, eq⟩ ↦ by simpa [← eq],
      fun h ↦ ⟨e.symm x, by simpa, RingEquiv.apply_symm_apply e x⟩⟩
    simpa only [Ideal.primeCompl, p]
  let _ := (isRegularRing_iff R).mp ‹_› p (Ideal.comap_isPrime e p')
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p) (Localization.AtPrime p') e this)
