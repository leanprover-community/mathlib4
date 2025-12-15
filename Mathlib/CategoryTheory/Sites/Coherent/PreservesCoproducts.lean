/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

@[expose] public section

open CategoryTheory Functor Limits GrothendieckTopology

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [Subcanonical J]
  {K : Type*} [Category K]
  [∀ X : Sheaf J (Type v), PreservesLimitsOfShape Kᵒᵖ X.val]

instance : PreservesColimitsOfShape K J.yoneda where
  preservesColimit {F} := { preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.yoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    suffices IsLimit ((X.val ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv
      (isoWhiskerRight (J.largeCurriedYonedaLemma) ((evaluation _ _ ).obj X)).symm this
    exact isLimitOfPreserves _ hc.op⟩ }

instance Subcanonical.preservesFiniteCoproductsYoneda
    [∀ X : Sheaf J (Type v), PreservesFiniteProducts X.val] :
    PreservesFiniteCoproducts J.yoneda where
  preserves _ := inferInstance
