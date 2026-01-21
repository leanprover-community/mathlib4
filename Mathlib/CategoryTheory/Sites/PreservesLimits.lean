/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!
# Preservation of (co)limits by the Yoneda functor
-/

@[expose] public section

open CategoryTheory Functor Limits GrothendieckTopology

universe v' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [Subcanonical J]
  {K : Type*} [Category K]

instance [∀ X : Sheaf J (Type v), PreservesLimitsOfShape Kᵒᵖ X.val] :
    PreservesColimitsOfShape K J.yoneda where
  preservesColimit {F} := { preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.yoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    suffices IsLimit ((X.val ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv
      (isoWhiskerRight (J.yonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isLimitOfPreserves _ hc.op⟩ }

instance [∀ X : Sheaf J (Type v), PreservesColimitsOfShape Kᵒᵖ X.val] :
    PreservesLimitsOfShape K J.yoneda where
  preservesLimit {F} := { preserves {c} hc := ⟨by
    suffices IsColimit (coyoneda.mapCocone (J.yoneda.mapCone c).op) from
      isLimitOfOp (isColimitOfReflects _ this)
    apply evaluationJointlyReflectsColimits
    intro X
    suffices IsColimit ((X.val ⋙ uliftFunctor).mapCocone c.op) from IsColimit.mapCoconeEquiv
      (isoWhiskerRight (J.yonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isColimitOfPreserves _ hc.op⟩ }

instance [abc : ∀ X : Sheaf J (Type (max v v')), PreservesLimitsOfShape Kᵒᵖ X.val] :
    PreservesColimitsOfShape K (GrothendieckTopology.uliftYoneda.{v', v, u} J) where
  preservesColimit {F} := { preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.uliftYoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    suffices IsLimit ((X.val ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv
      (isoWhiskerRight (J.uliftYonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isLimitOfPreserves _ hc.op⟩ }

instance [∀ X : Sheaf J (Type (max v v')), PreservesColimitsOfShape Kᵒᵖ X.val] :
    PreservesLimitsOfShape K (GrothendieckTopology.uliftYoneda.{v', v, u} J) where
  preservesLimit {F} := { preserves {c} hc := ⟨by
    suffices IsColimit (coyoneda.mapCocone (J.uliftYoneda.mapCone c).op) from
      isLimitOfOp (isColimitOfReflects _ this)
    apply evaluationJointlyReflectsColimits
    intro X
    suffices IsColimit ((X.val ⋙ uliftFunctor).mapCocone c.op) from IsColimit.mapCoconeEquiv
      (isoWhiskerRight (J.uliftYonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isColimitOfPreserves _ hc.op⟩ }
