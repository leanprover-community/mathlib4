/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.RingHom.Finite

/-! # Instances about extensions of fraction rings -/

variable {R₀ R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [IsDomain R] [IsDomain S] [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]

open scoped nonZeroDivisors

noncomputable section

instance : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra _ _

instance : IsScalarTower R₀ (FractionRing R) (FractionRing S) :=
  .of_algebraMap_eq' <| by
    simp [RingHom.algebraMap_toAlgebra, IsFractionRing.lift, ← RingHom.comp_assoc,
      IsScalarTower.algebraMap_eq R₀ R (FractionRing S),
      IsScalarTower.algebraMap_eq R₀ R (FractionRing R),
      IsScalarTower.algebraMap_eq R S (FractionRing S)]

instance [IsDomain R₀] [FaithfulSMul R₀ R] [FaithfulSMul R₀ S] :
    IsScalarTower (FractionRing R₀) (FractionRing R) (FractionRing S) :=
  .of_algebraMap_eq' <| by
    apply IsFractionRing.injective_comp_algebraMap (A := R₀)
    dsimp [RingHom.algebraMap_toAlgebra, IsFractionRing.lift]
    rw [RingHom.comp_assoc, IsLocalization.lift_comp, IsLocalization.lift_comp,
      IsScalarTower.algebraMap_eq R₀ R (FractionRing R), ← RingHom.comp_assoc,
      IsLocalization.lift_comp, IsScalarTower.algebraMap_eq R₀ R (FractionRing S)]

instance [Algebra.IsIntegral R S] : Algebra.IsIntegral (FractionRing R) (FractionRing S) :=
  Algebra.IsIntegral.of_isLocalization R S _ _ R⁰

instance [Module.Finite R S] : FiniteDimensional (FractionRing R) (FractionRing S) :=
  Module.Finite_of_isLocalization R S _ _ R⁰
