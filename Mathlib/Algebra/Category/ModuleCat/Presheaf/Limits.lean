/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Limits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `PresheafOfModules R`.

## TODO
* do the same for colimits

-/

universe w' w v₁ v₂ v u₁ u₂ u

namespace AddCommGroupCat

open CategoryTheory

instance : (forget AddCommGroupCat).ReflectsIsomorphisms := inferInstance

end AddCommGroupCat

namespace ModuleCat

open CategoryTheory Limits


section

variable (R : Type w) [Ring R] (J : Type u₂) [Category.{v₂} J]

instance (F : J ⥤ ModuleCat.{w'} R) [HasLimit (F ⋙ forget₂ _ AddCommGroupCat)] :
    HasLimit F := sorry
instance (F : J ⥤ ModuleCat.{w'} R) [HasLimit (F ⋙ forget₂ _ AddCommGroupCat)] :
    PreservesLimit F (forget _) := sorry

instance : (forget (ModuleCat R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f
      (asIso ((forget (ModuleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIso).hom)

instance : (forget₂ (ModuleCat.{w'} R) AddCommGroupCat.{w'}).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommGroupCat).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)

noncomputable instance {R : Type w} [Ring R] {J : Type u₂} [Category.{v₂} J]
    (F : J ⥤ ModuleCat.{w'} R) [PreservesLimit F (forget₂ (ModuleCat R) AddCommGroupCat)]
    [HasLimit F] :
    ReflectsLimit F (forget₂ (ModuleCat R) AddCommGroupCat) := by
  apply reflectsLimitOfReflectsIsomorphisms

end

noncomputable instance preservesLimitRestrictScalars
    {R : Type w} {S : Type u} [Ring R] [Ring S] (f : R →+* S) {J : Type u₂} [Category.{v₂} J]
    (F : J ⥤ ModuleCat.{w'} S) [HasLimit (F ⋙ forget₂ _ AddCommGroupCat)] :
    PreservesLimit F (restrictScalars.{w'} f) := sorry

--noncomputable instance preservesLimitsOfShapeRestrictScalars
--    {R : Type w} {S : Type u} [Ring R] [Ring S] (J : Type u₂) [Category.{v₂} J]
--    [PreservesLimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGroupCat.{w'})]
--    [PreservesLimitsOfShape J (forget₂ (ModuleCat.{w'} S) AddCommGroupCat.{w'})] (f : R →+* S) :
--    PreservesLimitsOfShape J  (restrictScalars.{w'} f) where
--  preservesLimit {K} := ⟨fun {c} hc => by
--    have : HasLimit ((K ⋙ restrictScalars f) ⋙ forget₂ _ AddCommGroupCat) :=
--      ⟨_, (isLimitOfPreserves (forget₂ (ModuleCat.{w'} S) AddCommGroupCat.{w'}) hc)⟩
--    exact isLimitOfReflects (forget₂ (ModuleCat.{w'} R) AddCommGroupCat.{w'})
--      (isLimitOfPreserves (forget₂ (ModuleCat.{w'} S) AddCommGroupCat.{w'}) hc)⟩

end ModuleCat

namespace PresheafOfModules

open CategoryTheory Category Limits

section Limits

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
  {J : Type u₂} [Category.{v₂} J] (F : J ⥤ PresheafOfModules.{w'} R)
  [∀ X, HasLimit (F ⋙ evaluation R X ⋙ forget₂ _ AddCommGroupCat)]
  --[∀ (X : Cᵒᵖ), PreservesLimitsOfShape J
  --  (forget₂ (ModuleCat.{w'} (R.obj X)) AddCommGroupCat.{w'})]

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
    HasLimit (F ⋙ evaluation R Y ⋙ ModuleCat.restrictScalars.{w'} (R.map f)) := by
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
    PreservesLimit F (evaluation R X : PresheafOfModules.{w'} R ⥤ _) :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (limit.isLimit _)

end

section

variable (R J)

-- this assumption should be found automatically in suitable universes
variable [HasLimitsOfShape J (AddCommGroupCat.{w'} )]

instance hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{w'} R) where

noncomputable def evaluationPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (evaluation R X : PresheafOfModules.{w'} R ⥤ _) where

end

instance : HasFiniteLimits (PresheafOfModules.{w'} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance (X : Cᵒᵖ) : PreservesFiniteLimits (evaluation.{w'} R X) where
  preservesFiniteLimits J _ _ := evaluationPreservesLimitsOfShape.{w'} R J X

end Limits

end PresheafOfModules
