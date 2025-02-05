/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!

# Localization and separability

This file contains results about the separability field of fraction of localizations.

## Main results

 * `map_mul Ideal.relNorm`: multiplicativity of the relative ideal norm
-/

attribute [local instance] FractionRing.liftAlgebra

open scoped nonZeroDivisors

variable {R : Type*} (S Rₘ Sₘ : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [CommRing Rₘ] [CommRing Sₘ]  [Algebra R Rₘ] [Algebra R S] [NoZeroSMulDivisors R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] {M : Submonoid R} [IsLocalization M Rₘ]
    [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    [Algebra (FractionRing Rₘ) (FractionRing Sₘ)]
    [IsScalarTower Rₘ (FractionRing Rₘ) (FractionRing Sₘ)]

include R S in
theorem FractionRing.isSeparable_of_isLocalization (hM : M ≤ R⁰) :
    Algebra.IsSeparable (FractionRing Rₘ) (FractionRing Sₘ) := by
  let K := FractionRing R
  let L := FractionRing S
  let M' := Algebra.algebraMapSubmonoid S M
  have hM' : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _) hM
  let f₁ : Rₘ →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let f₂ : Sₘ →+* L := IsLocalization.map _ (T := S⁰) (RingHom.id S) hM'
  algebraize [f₁, f₂]
  have := IsLocalization.localization_isScalarTower_of_submonoid_le Rₘ K _ _ hM
  have := IsLocalization.localization_isScalarTower_of_submonoid_le Sₘ L _ _ hM'
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M' Sₘ L
  have : IsDomain Rₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  apply Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Rₘ K).symm.toRingEquiv
    (FractionRing.algEquiv Sₘ L).symm.toRingEquiv
  apply IsLocalization.ringHom_ext R⁰
  ext
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply R Rₘ (FractionRing R), AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, IsScalarTower.algebraMap_apply R S L,
      IsScalarTower.algebraMap_apply S Sₘ L, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  simp only [← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply R Rₘ (FractionRing Rₘ), ← IsScalarTower.algebraMap_apply Rₘ,
      ← IsScalarTower.algebraMap_apply]

include R S in
theorem IsFractionRing.isSeparable_of_isLocalization {Kₘ Lₘ : Type*} [Field Kₘ] [Field Lₘ]
    [Algebra Rₘ Kₘ] [Algebra Sₘ Lₘ] [IsFractionRing Rₘ Kₘ] [IsFractionRing Sₘ Lₘ] [Algebra Kₘ Lₘ]
    [Algebra Rₘ Lₘ] [IsScalarTower Rₘ Kₘ Lₘ] [IsScalarTower Rₘ Sₘ Lₘ]
    (hM : M ≤ R⁰) : Algebra.IsSeparable Kₘ Lₘ := by
  have hM' : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _) hM
  let f₁ : FractionRing Rₘ ≃+* Kₘ := FractionRing.algEquiv Rₘ Kₘ
  let f₂ : FractionRing Sₘ ≃+* Lₘ := FractionRing.algEquiv Sₘ Lₘ
  have : IsDomain Rₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM'
  have : Algebra.IsSeparable (FractionRing Rₘ) (FractionRing Sₘ) :=
    FractionRing.isSeparable_of_isLocalization S Rₘ Sₘ hM
  apply Algebra.IsSeparable.of_equiv_equiv f₁ f₂
  dsimp [f₁, f₂]
  rw [← FractionRing.algEquiv_comp_algebraMap Rₘ Kₘ Sₘ]
