/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.away.adjoin_root
! leanprover-community/mathlib commit a7c017d750512a352b623b1824d75da5998457d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic

/-!
The `R`-`alg_equiv` between the localization of `R` away from `r` and
`R` with an inverse of `r` adjoined.
-/


open Polynomial AdjoinRoot Localization

variable {R : Type _} [CommRing R]

attribute [local instance] IsLocalization.algHom_subsingleton AdjoinRoot.algHom_subsingleton

/-- The `R`-`alg_equiv` between the localization of `R` away from `r` and
    `R` with an inverse of `r` adjoined. -/
noncomputable def Localization.awayEquivAdjoin (r : R) : Away r ≃ₐ[R] AdjoinRoot (C r * X - 1) :=
  AlgEquiv.ofAlgHom
    { awayLift _ r _ with
      commutes' :=
        IsLocalization.Away.AwayMap.lift_eq r (isUnit_of_mul_eq_one _ _ <| root_is_inv r) }
    (liftHom _ (IsLocalization.Away.invSelf r) <| by
      simp only [map_sub, map_mul, aeval_C, aeval_X, IsLocalization.Away.mul_invSelf, aeval_one,
        sub_self])
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
#align localization.away_equiv_adjoin Localization.awayEquivAdjoin

theorem IsLocalization.adjoin_inv (r : R) : IsLocalization.Away r (AdjoinRoot <| C r * X - 1) :=
  IsLocalization.isLocalization_of_algEquiv _ (Localization.awayEquivAdjoin r)
#align is_localization.adjoin_inv IsLocalization.adjoin_inv

theorem IsLocalization.Away.finitePresentation (r : R) {S} [CommRing S] [Algebra R S]
    [IsLocalization.Away r S] : Algebra.FinitePresentation R S :=
  (AdjoinRoot.finitePresentation _).Equiv <|
    (Localization.awayEquivAdjoin r).symm.trans <| IsLocalization.algEquiv (Submonoid.powers r) _ _
#align is_localization.away.finite_presentation IsLocalization.Away.finitePresentation

