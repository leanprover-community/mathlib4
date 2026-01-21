/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
The `R`-`AlgEquiv` between the localization of `R` away from `r` and
`R` with an inverse of `r` adjoined.
-/

@[expose] public section

open Polynomial AdjoinRoot Localization

variable {R : Type*} [CommRing R]

attribute [local instance] AdjoinRoot.algHom_subsingleton

/-- The `R`-`AlgEquiv` between the localization of `R` away from `r` and
`R` with an inverse of `r` adjoined. -/
noncomputable def Localization.awayEquivAdjoin (r : R) : Away r ≃ₐ[R] AdjoinRoot (C r * X - 1) :=
  AlgEquiv.ofAlgHom
    { awayLift _ r _ with
      commutes' :=
        IsLocalization.Away.lift_eq r (.of_mul_eq_one _ <| root_isInv r) }
    (liftAlgHom _ (Algebra.ofId _ _) (IsLocalization.Away.invSelf r) <| show aeval _ _ = _ by simp)
    (Subsingleton.elim _ _)
    (Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers r)) _ _)

theorem IsLocalization.adjoin_inv (r : R) : IsLocalization.Away r (AdjoinRoot <| C r * X - 1) :=
  IsLocalization.isLocalization_of_algEquiv _ (Localization.awayEquivAdjoin r)

theorem IsLocalization.Away.finitePresentation (r : R) {S} [CommRing S] [Algebra R S]
    [IsLocalization.Away r S] : Algebra.FinitePresentation R S :=
  (AdjoinRoot.finitePresentation _).equiv <|
    (Localization.awayEquivAdjoin r).symm.trans <| IsLocalization.algEquiv (Submonoid.powers r) _ _

lemma Algebra.FinitePresentation.of_isLocalizationAway
    {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    [Algebra S S'] [IsScalarTower R S S'] (f : S) [IsLocalization.Away f S']
    [Algebra.FinitePresentation R S] :
    Algebra.FinitePresentation R S' :=
  have : Algebra.FinitePresentation S S' :=
    IsLocalization.Away.finitePresentation f
  .trans R S S'

instance {S : Type*} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (f : S) :
    Algebra.FinitePresentation R (Localization.Away f) :=
  .of_isLocalizationAway f
