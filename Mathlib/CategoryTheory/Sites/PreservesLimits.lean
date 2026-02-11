/-
Copyright (c) 2026 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!

# Preservation of (co)limits by the sheaf Yoneda functor
-/

@[expose] public section

open CategoryTheory Functor Limits GrothendieckTopology

universe v' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [Subcanonical J]
  {K : Type*} [Category* K]

<<<<<<< HEAD
instance {F : K ⥤ C} [∀ X : Sheaf J (Type max v v'), PreservesLimit F.op X.val] :
=======
instance {F : K ⥤ C} [∀ X : Sheaf J (Type v), PreservesLimit F.op X.val] :
    PreservesColimit F J.yoneda where
  preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.yoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    suffices IsLimit ((X.val ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv
      (isoWhiskerRight (J.yonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isLimitOfPreserves _ hc.op⟩

instance [∀ X : Sheaf J (Type v), PreservesLimitsOfShape Kᵒᵖ X.val] :
    PreservesColimitsOfShape K J.yoneda where
  preservesColimit := inferInstance

instance {F : K ⥤ C} [∀ X : Sheaf J (Type (max v v')), PreservesLimit F.op X.val] :
>>>>>>> 7df768e8d3 (General limit preservation)
    PreservesColimit F (GrothendieckTopology.uliftYoneda.{v', v, u} J) where
  preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.uliftYoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    suffices IsLimit ((X.val ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv
      (isoWhiskerRight (J.uliftYonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isLimitOfPreserves _ hc.op⟩

<<<<<<< HEAD
instance {F : K ⥤ C} [∀ X : Sheaf J (Type max v v'), PreservesColimit F.op X.val] :
    PreservesLimit F (GrothendieckTopology.uliftYoneda.{v', v, u} J) where
  preserves {c} hc := ⟨by
    suffices IsColimit (coyoneda.mapCocone (J.uliftYoneda.mapCone c).op) from
      isLimitOfOp (isColimitOfReflects _ this)
    apply evaluationJointlyReflectsColimits
    intro X
    suffices IsColimit ((X.val ⋙ uliftFunctor).mapCocone c.op) from IsColimit.mapCoconeEquiv
      (isoWhiskerRight (J.uliftYonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isColimitOfPreserves _ hc.op⟩

instance [∀ X : Sheaf J (Type max v v'), PreservesLimitsOfShape Kᵒᵖ X.val] :
=======
instance [∀ X : Sheaf J (Type (max v v')), PreservesLimitsOfShape Kᵒᵖ X.val] :
>>>>>>> 7df768e8d3 (General limit preservation)
    PreservesColimitsOfShape K (GrothendieckTopology.uliftYoneda.{v', v, u} J) where

<<<<<<< HEAD
instance [∀ X : Sheaf J (Type max v v'), PreservesColimitsOfShape Kᵒᵖ X.val] :
    PreservesLimitsOfShape K (GrothendieckTopology.uliftYoneda.{v', v, u} J) where
=======
instance : PreservesLimitsOfShape K J.yoneda where
  preservesLimit := by
    intro F
    have :
        PreservesLimitsOfShape K (J.yoneda ⋙ sheafToPresheaf J (Type v)) :=
      preservesLimitsOfShape_of_natIso
        (GrothendieckTopology.yonedaCompSheafToPresheaf J).symm
    apply preservesLimit_of_reflects_of_preserves
      (F := J.yoneda)
      (G := sheafToPresheaf ..)

instance : PreservesLimitsOfShape K (GrothendieckTopology.uliftYoneda.{v', v, u} J) where
  preservesLimit := by
    intro F
    have :
        PreservesLimitsOfShape K (GrothendieckTopology.uliftYoneda.{v', v, u} J ⋙
          sheafToPresheaf J (Type (max v v'))) :=
      preservesLimitsOfShape_of_natIso
        (GrothendieckTopology.uliftYonedaCompSheafToPresheaf J).symm
    apply preservesLimit_of_reflects_of_preserves
      (F := GrothendieckTopology.uliftYoneda.{v', v, u} J)
      (G := sheafToPresheaf ..)
>>>>>>> 7df768e8d3 (General limit preservation)

instance [∀ X : Sheaf J (Type max v v'), PreservesFiniteProducts X.val] :
    PreservesFiniteCoproducts (GrothendieckTopology.uliftYoneda.{v', v, u} J) where
  preserves _ := inferInstance

instance {F : K ⥤ C} [∀ X : Sheaf J (Type v), PreservesLimit F.op X.val] :
    PreservesColimit F J.yoneda :=
  preservesColimit_of_natIso _ J.uliftYonedaIsoYoneda

instance {F : K ⥤ C} [∀ X : Sheaf J (Type v), PreservesColimit F.op X.val] :
    PreservesLimit F J.yoneda :=
  preservesLimit_of_natIso _ J.uliftYonedaIsoYoneda

instance [∀ X : Sheaf J (Type v), PreservesLimitsOfShape Kᵒᵖ X.val] :
    PreservesColimitsOfShape K J.yoneda where

instance [∀ X : Sheaf J (Type v), PreservesColimitsOfShape Kᵒᵖ X.val] :
    PreservesLimitsOfShape K J.yoneda where

instance [∀ X : Sheaf J (Type v), PreservesFiniteProducts X.val] :
    PreservesFiniteCoproducts J.yoneda where
  preserves _ := inferInstance
