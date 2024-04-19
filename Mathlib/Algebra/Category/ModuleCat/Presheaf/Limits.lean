/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory

/-! # Limits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `PresheafOfModules R`.

## TODO
* do the same for colimits

-/

universe v v₁ v₂ u₁ u₂ u u'

namespace ModuleCat

open CategoryTheory Limits

section

variable {R : Type u} [Ring R] {J : Type u₂} [Category.{v₂} J]

section

variable (F : J ⥤ ModuleCat.{v} R) [HasLimit (F ⋙ forget₂ _ AddCommGroupCat)]

lemma small_sections_of_hasLimit_forget₂ :
    Small.{v} (F ⋙ forget (ModuleCat R)).sections := by
  change Small.{v} ((F ⋙ forget₂ _ AddCommGroupCat) ⋙ forget _).sections
  have : HasLimit (F ⋙ forget₂ _ AddCommGroupCat) := inferInstance
  --depends on `AddCommGroupCat.hasLimit_iff_small_sections` from #11669
  sorry

instance : HasLimit F := by
  have := small_sections_of_hasLimit_forget₂ F
  apply hasLimit

noncomputable instance : PreservesLimit F (forget₂ _ AddCommGroupCat) := by
  have := small_sections_of_hasLimit_forget₂ F
  infer_instance

end

instance : (forget (ModuleCat R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f
      (asIso ((forget (ModuleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIso).hom)

instance : (forget₂ (ModuleCat.{v} R) AddCommGroupCat.{v}).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommGroupCat).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)

noncomputable instance {R : Type u} [Ring R] {J : Type u₂} [Category.{v₂} J]
    (F : J ⥤ ModuleCat.{v} R) [HasLimit (F ⋙ forget₂ _ AddCommGroupCat)] :
    ReflectsLimit F (forget₂ (ModuleCat R) AddCommGroupCat) := by
  apply reflectsLimitOfReflectsIsomorphisms

end

noncomputable instance preservesLimitRestrictScalars
    {R : Type u} {S : Type u'} [Ring R] [Ring S] (f : R →+* S) {J : Type u₂} [Category.{v₂} J]
    (F : J ⥤ ModuleCat.{v} S) [HasLimit (F ⋙ forget₂ _ AddCommGroupCat)] :
    PreservesLimit F (restrictScalars f) :=
  ⟨fun {c} hc => by
    have : HasLimit ((F ⋙ restrictScalars f) ⋙ forget₂ (ModuleCat R) AddCommGroupCat) := by
      assumption
    have hc' := isLimitOfPreserves (forget₂ _ AddCommGroupCat) hc
    exact isLimitOfReflects (forget₂ _ AddCommGroupCat) hc'⟩

end ModuleCat

namespace PresheafOfModules

open CategoryTheory Category Limits

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]

section Limits

section

variable (F : J ⥤ PresheafOfModules.{v} R)
  [∀ X, HasLimit (F ⋙ evaluation R X ⋙ forget₂ _ AddCommGroupCat)]

instance (X : Cᵒᵖ) : HasLimit ((F ⋙ evaluation R X) ⋙ forget₂ _ AddCommGroupCat) := by
  change HasLimit (F ⋙ evaluation R X ⋙ forget₂ _ AddCommGroupCat)
  infer_instance

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

section

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasLimit (F ⋙ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f)) := by
  change HasLimit ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f))
  infer_instance

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

noncomputable def limitConeπApp (j : J) : (limitBundledCore F).toPresheafOfModules ⟶ F.obj j :=
  PresheafOfModules.Hom.mk'' (fun X => limit.π (F ⋙ evaluation R X) j) (fun X Y f => by
    dsimp
    simp only [assoc, preservesLimitsIso_inv_π]
    apply limMap_π)

@[reassoc (attr := simp)]
lemma limitConeπApp_naturality {i j : J} (f : i ⟶ j) :
    limitConeπApp F i ≫ F.map f = limitConeπApp F j := by
  ext1 X
  exact limit.w (F ⋙ evaluation R X) f

@[simps]
noncomputable def limitCone : Cone F where
  pt := (limitBundledCore F).toPresheafOfModules
  π := { app := limitConeπApp F }

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

end

end

section

variable (R J)

variable [HasLimitsOfShape J AddCommGroupCat.{v}]

instance hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{v} R) where

noncomputable def evaluationPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (evaluation R X : PresheafOfModules.{v} R ⥤ _) where

noncomputable def toPresheafPreservesLimitsOfShape :
    PreservesLimitsOfShape J (toPresheaf.{v} R) where

end

instance hasFiniteLimits : HasFiniteLimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance preservesFiniteLimitsEvaluation (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where
  preservesFiniteLimits J _ _ := evaluationPreservesLimitsOfShape.{v} R J X

noncomputable instance preservesFiniteLimitsToPresheaf :
    PreservesFiniteLimits (toPresheaf R) where
  preservesFiniteLimits _ _ _ := toPresheafPreservesLimitsOfShape _ _

end Limits

end PresheafOfModules
