/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!

# Definition of Gorenstein Local Ring

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

/-- A local ring `R` is Gorenstein if `R` itself viewed as an `R`-module
has finite injective dimension. -/
class IsGorensteinLocalRing : Prop extends IsLocalRing R where
  injdim : injectiveDimension (ModuleCat.of R R) ≠ ⊤

lemma isGorensteinLocalRing_def [IsLocalRing R] :
    IsGorensteinLocalRing R ↔ injectiveDimension (ModuleCat.of R R) ≠ ⊤ :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

variable {R} in
attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma IsGorensteinLocalRing.of_ringEquiv {R' : Type u} [CommRing R'] (e : R ≃+* R')
    [IsGorensteinLocalRing R] : IsGorensteinLocalRing R' := by
  let eR : (ModuleCat.of R R) ≃ₛₗ[RingHomClass.toRingHom e] (ModuleCat.of R' R') :=
    e.toSemilinearEquiv
  have : IsLocalRing R' := e.isLocalRing
  have := (isGorensteinLocalRing_def R).mp ‹_›
  rw [injectiveDimension_eq_of_semiLinearEquiv e eR] at this
  exact (isGorensteinLocalRing_def R').mpr this

/-- A commutative ring is Gorenstein if its localization at every prime
`IsGorensteinLocalRing`. -/
class IsGorensteinRing : Prop where
  isGorenstein_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime),
    IsGorensteinLocalRing (Localization.AtPrime p)

lemma isGorensteinRing_def : IsGorensteinRing R ↔
    ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsGorensteinLocalRing (Localization.AtPrime p) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isGorensteinRing_def' : IsGorensteinRing R ↔
    ∀ p : PrimeSpectrum R, IsGorensteinLocalRing (Localization.AtPrime p.1) :=
  ⟨fun ⟨h⟩ ↦ fun p ↦ h p.1 p.2, fun h ↦ ⟨fun p hp ↦ h ⟨p, hp⟩⟩⟩

lemma isGorensteinRing_of_ringEquiv {R' : Type u} [CommRing R']
    (e : R ≃+* R') [G : IsGorensteinRing R] : IsGorensteinRing R' := by
  apply (isGorensteinRing_def R').mpr (fun p' hp' ↦ ?_)
  let p := p'.comap e
  have := (isGorensteinRing_def R).mp ‹_› p (Ideal.comap_isPrime e p')
  have : p.primeCompl.map e.toMonoidHom = p'.primeCompl := by
    ext x
    have : (∃ y, e y ∉ p' ∧ e y = x) ↔ x ∉ p' := ⟨fun ⟨y, hy, eq⟩ ↦ eq ▸ hy,
      fun h ↦ ⟨e.symm x, (RingEquiv.apply_symm_apply e x).symm ▸ h, RingEquiv.apply_symm_apply e x⟩⟩
    simpa only [p]
  exact IsGorensteinLocalRing.of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p) (Localization.AtPrime p') e this)
