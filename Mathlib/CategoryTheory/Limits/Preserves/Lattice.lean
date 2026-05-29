/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Lattice Homs that Preserve Limits and Colimits

-/

public section

open OrderHomClass

namespace CategoryTheory.Limits.CompleteLattice

universe w w' u v

variable {α : Type u} {β : Type v} {F : Type*} [FunLike F α β] (f : F)

section

variable [SemilatticeInf α] [OrderTop α] [SemilatticeInf β] [OrderTop β] [InfTopHomClass F α β]

instance preservesLimit_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor :=
  preservesLimit_of_preserves_limit_cone (finiteLimitCone K).isLimit <|
    (finiteLimitCone _).isLimit.ofIsoLimit
      (Cone.ext (eqToIso (by aesop : Finset.univ.inf _ = f _)) (by subsingleton))

instance preservesLimitsOfShape_finite_toFunctor {J : Type w} [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J (toOrderHom f).toFunctor where

instance : PreservesFiniteLimits (toOrderHom f).toFunctor where
  preservesFiniteLimits _ _ _ := inferInstance

end

section

variable [SemilatticeSup α] [OrderBot α] [SemilatticeSup β] [OrderBot β] [SupBotHomClass F α β]

instance preservesColimit_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor :=
  preservesColimit_of_preserves_colimit_cocone (finiteColimitCocone K).isColimit <|
    (finiteColimitCocone _).isColimit.ofIsoColimit
      (Cocone.ext (eqToIso (by aesop : Finset.univ.sup _ = f _)) (by subsingleton))

instance preservesColimitsOfShape_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] : PreservesColimitsOfShape J (toOrderHom f).toFunctor where

instance : PreservesFiniteColimits (toOrderHom f).toFunctor where
  preservesFiniteColimits _ _ _ := inferInstance

end

section

variable [CompleteLattice α] [CompleteLattice β]

instance preservesLimit_toFunctor [sInfHomClass F α β] {J : Type w} [Category.{w'} J]
    (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor :=
  preservesLimit_of_preserves_limit_cone (limitCone K).isLimit <|
    (limitCone _).isLimit.ofIsoLimit (Cone.ext (eqToIso (by aesop)) (by subsingleton))

instance preservesLimitsOfShape_toFunctor [sInfHomClass F α β] {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J (toOrderHom f).toFunctor where

instance preservesLimitsOfSize_toFunctor [sInfHomClass F α β] :
    PreservesLimitsOfSize.{w', w} (toOrderHom f).toFunctor where

instance preservesLimits_toFunctor [sInfHomClass F α β] :
    PreservesLimits (toOrderHom f).toFunctor where

instance preservesColimit_toFunctor [sSupHomClass F α β] {J : Type w} [Category.{w'} J]
    (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor :=
  preservesColimit_of_preserves_colimit_cocone (colimitCocone K).isColimit <|
    (colimitCocone _).isColimit.ofIsoColimit (Cocone.ext (eqToIso (by aesop)) (by subsingleton))

instance preservesColimitsOfShape_toFunctor [sSupHomClass F α β] {J : Type w} [Category.{w'} J] :
    PreservesColimitsOfShape J (toOrderHom f).toFunctor where

instance preservesColimitsOfSize_toFunctor [sSupHomClass F α β] :
    PreservesColimitsOfSize.{w', w} (toOrderHom f).toFunctor where

instance preservesColimits_toFunctor [sSupHomClass F α β] :
    PreservesColimits (toOrderHom f).toFunctor where

end

end CategoryTheory.Limits.CompleteLattice
