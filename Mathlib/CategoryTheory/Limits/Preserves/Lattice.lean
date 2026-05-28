/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Complete Lattice Homs Preserve Limits and Colimits

-/

public section

open CategoryTheory Limits OrderHomClass

namespace CategoryTheory.Limits.CompleteLattice

universe w w' u v

variable {α : Type u} {β : Type v} [CompleteLattice α] [CompleteLattice β]
  {F : Type*} [FunLike F α β] [CompleteLatticeHomClass F α β] (f : F)

instance preservesLimit_toFunctor {J : Type w} [Category.{w'} J]
    (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor :=
  preservesLimit_of_preserves_limit_cone (limitCone K).isLimit <|
    (limitCone _).isLimit.ofIsoLimit (Cone.ext (eqToIso (by aesop)) (by subsingleton))

instance preservesLimitsOfShape_toFunctor {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J (toOrderHom f).toFunctor where

instance preservesLimitsOfSize_toFunctor :
    PreservesLimitsOfSize.{w', w} (toOrderHom f).toFunctor where

instance preservesLimits_toFunctor :
    PreservesLimits (toOrderHom f).toFunctor where

instance preservesColimit_toFunctor {J : Type w} [Category.{w'} J]
    (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor :=
  preservesColimit_of_preserves_colimit_cocone (colimitCocone K).isColimit <|
    (colimitCocone _).isColimit.ofIsoColimit (Cocone.ext (eqToIso (by aesop)) (by subsingleton))

instance preservesColimitsOfShape_toFunctor {J : Type w} [Category.{w'} J] :
    PreservesColimitsOfShape J (toOrderHom f).toFunctor where

instance preservesColimitsOfSize_toFunctor :
    PreservesColimitsOfSize.{w', w} (toOrderHom f).toFunctor where

instance preservesColimits_toFunctor :
    PreservesColimits (toOrderHom f).toFunctor where

end CategoryTheory.Limits.CompleteLattice
