/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yakov Pechersky
-/
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.RingHom.Finite

/-! # Instances about extensions of fraction rings -/

variable {R₀ R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [IsDomain S] [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]

open scoped nonZeroDivisors

namespace FractionRing

noncomputable section

/-- This causes a diamond for `Algebra (FractionRing R) (FractionRing (FractionRing R))`
but we will hardly ever see `FractionRing (FractionRing R)` in mathlib. -/
instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra _ _

lemma algebraMap_fractionRing_eq_map :
    algebraMap (FractionRing R) (FractionRing S) =
      IsFractionRing.map (FaithfulSMul.algebraMap_injective R S) :=
  rfl

instance : IsScalarTower R₀ (FractionRing R) (FractionRing S) :=
  .of_algebraMap_eq' <| by
    simp [algebraMap_fractionRing_eq_map, IsFractionRing.map, ← RingHom.comp_assoc,
      IsScalarTower.algebraMap_eq R₀ R (FractionRing S),
      IsScalarTower.algebraMap_eq R₀ R (FractionRing R),
      IsScalarTower.algebraMap_eq R S (FractionRing S)]

instance [FaithfulSMul R₀ R] [FaithfulSMul R₀ S] :
    haveI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
    IsScalarTower (FractionRing R₀) (FractionRing R) (FractionRing S) :=
  haveI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext R₀⁰
    dsimp [algebraMap_fractionRing_eq_map, IsFractionRing.map]
    rw [RingHom.comp_assoc, IsLocalization.map_comp, IsLocalization.map_comp,
      ← RingHom.comp_assoc, IsLocalization.map_comp, RingHom.comp_assoc,
      IsScalarTower.algebraMap_eq R₀ R S]

instance [Algebra.IsIntegral R S] :
    Algebra.IsIntegral (FractionRing R) (FractionRing S) :=
  haveI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  Algebra.IsIntegral.of_isLocalization R S _ _ R⁰

instance [Module.Finite R S] :
    haveI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
    FiniteDimensional (FractionRing R) (FractionRing S) :=
  haveI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  Module.Finite_of_isLocalization R S _ _ R⁰

-- TODO: add statement about how rank of `FractionRing S` as an `FractionRing R`-module
-- relates to the rank of `S` as an `R`-module, after #22966

end

end FractionRing
