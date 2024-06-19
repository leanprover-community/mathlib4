/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory

/-! # Limits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `PresheafOfModules R`.

-/

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Limits

variable [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]

/-- A cone in the category `PresheafOfModules R` is limit if it is so after the application
of the functors `evaluation R X` for all `X`. -/
def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : ∀ (X : Cᵒᵖ), IsLimit ((evaluation R X).mapCone c)) : IsLimit c where
  lift s := Hom.mk'' (fun X => (hc X).lift ((evaluation R X).mapCone s)) (fun X Y f => by
    apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f)) (hc Y)).hom_ext
    intro j
    rw [Functor.mapCone_π_app, assoc, assoc, ← Functor.map_comp]
    erw [restrictionApp_naturality, IsLimit.fac, restrictionApp_naturality, IsLimit.fac_assoc]
    rfl)
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm]
    rfl

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasLimit (F ⋙ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f)) := by
  change HasLimit ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f))
  infer_instance

set_option backward.isDefEq.lazyWhnfCore false in -- See https://github.com/leanprover-community/mathlib4/issues/12534
/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the `BundledCorePresheafOfModules R` which
corresponds to the presheaf of modules which sends `X` to the limit of `F ⋙ evaluation R X`. -/
@[simps]
noncomputable def limitBundledCore : BundledCorePresheafOfModules R where
  obj X := limit (F ⋙ evaluation R X)
  map {X Y} f := limMap (whiskerLeft F (restriction R f)) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (R.map f)) (F ⋙ evaluation R Y)).inv
  map_id X := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    dsimp
    simp only [limMap_π, Functor.comp_obj, evaluation_obj, whiskerLeft_app,
      restriction_app, assoc]
    erw [preservesLimitsIso_hom_π]
    rw [← ModuleCat.restrictScalarsId'App_inv_naturality, restrictionApp_id]
    dsimp
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, assoc, assoc, assoc, Iso.inv_hom_id,
      comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.comp_obj, evaluation_obj, limMap_π, whiskerLeft_app, restriction_app,
      Functor.map_comp, assoc, restrictionApp_comp]
    erw [preservesLimitsIso_hom_π, ← ModuleCat.restrictScalarsComp'App_inv_naturality]
    dsimp
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, assoc,
      preservesLimitsIso_inv_π]
    erw [limMap_π]
    dsimp
    simp only [Functor.map_comp, assoc, preservesLimitsIso_inv_π_assoc]
    erw [limMap_π_assoc]
    dsimp

/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the canonical map
`(limitBundledCore F).toPresheafOfModules ⟶ F.obj j` for all `j : J`. -/
noncomputable def limitConeπApp (j : J) :
    (limitBundledCore F).toPresheafOfModules ⟶ F.obj j :=
  PresheafOfModules.Hom.mk'' (fun X => limit.π (F ⋙ evaluation R X) j) (fun X Y f => by
    dsimp
    simp only [assoc, preservesLimitsIso_inv_π]
    apply limMap_π)

@[reassoc (attr := simp)]
lemma limitConeπApp_naturality {i j : J} (f : i ⟶ j) :
    limitConeπApp F i ≫ F.map f = limitConeπApp F j := by
  ext1 X
  exact limit.w (F ⋙ evaluation R X) f

/-- The (limit) cone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed for the limit
of `F ⋙ evaluation R X` for all `X`. -/
@[simps]
noncomputable def limitCone : Cone F where
  pt := (limitBundledCore F).toPresheafOfModules
  π := { app := limitConeπApp F }

/-- The cone `limitCone F` is limit for any `F : J ⥤ PresheafOfModules.{v} R`. -/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

instance hasLimit : HasLimit F := ⟨_, isLimitLimitCone F⟩

noncomputable instance evaluationPreservesLimit (X : Cᵒᵖ) :
    PreservesLimit F (evaluation R X) :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (limit.isLimit _)

noncomputable instance toPresheafPreservesLimit :
    PreservesLimit F (toPresheaf R) :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F)
    (Limits.evaluationJointlyReflectsLimits _
      (fun X => isLimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGroupCat)
        (isLimitLimitCone F)))

end Limits

variable (R J)

section Small

variable [Small.{v} J]

instance hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{v} R) where

noncomputable instance evaluationPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (evaluation R X : PresheafOfModules.{v} R ⥤ _) where

noncomputable instance toPresheafPreservesLimitsOfShape :
    PreservesLimitsOfShape J (toPresheaf.{v} R) where

end Small

namespace Finite

instance hasFiniteLimits : HasFiniteLimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance evaluationPreservesFiniteLimits (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where

noncomputable instance toPresheafPreservesFiniteLimits :
    PreservesFiniteLimits (toPresheaf R) where

end Finite

end PresheafOfModules
