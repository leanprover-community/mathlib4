/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!

# Definition of Gorenstein Local Ring

In this file, we defined the concept of Gorenstein local rings which are the local rings itself
having finite injective dimension as module.

# Main definition and results

* `IsGorensteinLocalRing` : The local ring with `injectiveDimension (ModuleCat.of R R) ≠ ⊤`.

* `IsGorensteinRing` : The ring whose all localizations at primes are Gorenstein local rings.

-/

public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

/-- A local ring `R` is Gorenstein if `R` itself viewed as an `R`-module
has finite injective dimension. -/
class IsGorensteinLocalRing : Prop extends IsLocalRing R where
  injdim : injectiveDimension (ModuleCat.of R R) ≠ ⊤

lemma isGorensteinLocalRing_iff [IsLocalRing R] :
    IsGorensteinLocalRing R ↔ injectiveDimension (ModuleCat.of R R) ≠ ⊤ :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

variable {R} in
attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma IsGorensteinLocalRing.of_ringEquiv {R' : Type v} [CommRing R'] (e : R ≃+* R')
    [IsGorensteinLocalRing R] : IsGorensteinLocalRing R' := by
  let eR : (ModuleCat.of R R) ≃ₛₗ[RingHomClass.toRingHom e] (ModuleCat.of R' R') :=
    e.toSemilinearEquiv
  have : IsLocalRing R' := e.isLocalRing
  have := (isGorensteinLocalRing_iff R).mp ‹_›
  rw [ModuleCat.injectiveDimension_eq_of_semiLinearEquiv e eR] at this
  exact (isGorensteinLocalRing_iff R').mpr this

/-- A commutative ring is Gorenstein if its localization at every prime
`IsGorensteinLocalRing`. -/
@[mk_iff]
class IsGorensteinRing : Prop where
  isGorenstein_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime),
    IsGorensteinLocalRing (Localization.AtPrime p)

lemma isGorensteinRing_iff' : IsGorensteinRing R ↔
    ∀ p : PrimeSpectrum R, IsGorensteinLocalRing (Localization.AtPrime p.1) :=
  ⟨fun ⟨h⟩ ↦ fun p ↦ h p.1 p.2, fun h ↦ ⟨fun p hp ↦ h ⟨p, hp⟩⟩⟩

lemma isGorensteinRing_of_ringEquiv {R' : Type u} [CommRing R']
    (e : R ≃+* R') [G : IsGorensteinRing R] : IsGorensteinRing R' := by
  apply (isGorensteinRing_iff R').mpr (fun p' hp' ↦ ?_)
  have := (isGorensteinRing_iff R).mp ‹_› (p'.comap e) (Ideal.comap_isPrime e p')
  exact IsGorensteinLocalRing.of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (p'.comap e))
      (Localization.AtPrime p') e (e.map_primeCompl_comap_eq p'))
