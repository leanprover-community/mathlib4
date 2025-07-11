/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

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
  lift s :=
    { app := fun X => (hc X).lift ((evaluation R X).mapCone s)
      naturality := fun {X Y} f ↦ by
        apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom) (hc Y)).hom_ext
        intro j
        have h₁ := (c.π.app j).naturality f
        have h₂ := (hc X).fac ((evaluation R X).mapCone s) j
        rw [Functor.mapCone_π_app, assoc, assoc, ← Functor.map_comp, IsLimit.fac]
        dsimp at h₁ h₂ ⊢
        rw [h₁, reassoc_of% h₂, Hom.naturality] }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm, comp_app]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasLimit (F ⋙ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f).hom) := by
  change HasLimit ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f).hom)
  infer_instance

/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the presheaf of modules obtained by
taking a limit in the category of modules over `R.obj X` for all `X`. -/
@[simps]
noncomputable def limitPresheafOfModules : PresheafOfModules R where
  obj X := limit (F ⋙ evaluation R X)
  map {_ Y} f := limMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    dsimp
    simp only [limMap_π, Functor.comp_obj, evaluation_obj, Functor.whiskerLeft_app,
      restriction_app, assoc]
    -- Here we should rewrite using `Functor.assoc` but that gives a "motive is type-incorrect"
    erw [preservesLimitIso_hom_π]
    rw [← ModuleCat.restrictScalarsId'App_inv_naturality, map_id,
      ModuleCat.restrictScalarsId'_inv_app]
    dsimp
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, assoc, assoc, assoc, Iso.inv_hom_id,
      comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.comp_obj, evaluation_obj, limMap_π, Functor.whiskerLeft_app, restriction_app,
      map_comp, ModuleCat.restrictScalarsComp'_inv_app, Functor.map_comp, assoc]
    -- Here we should rewrite using `Functor.assoc` but that gives a "motive is type-incorrect"
    erw [preservesLimitIso_hom_π]
    rw [← ModuleCat.restrictScalarsComp'App_inv_naturality]
    dsimp
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, assoc,
      preservesLimitIso_inv_π]
    -- Here we should rewrite using `Functor.assoc` but that gives a "motive is type-incorrect"
    erw [limMap_π]
    dsimp
    simp only [Functor.map_comp, assoc, preservesLimitIso_inv_π_assoc]
    -- Here we should rewrite using `Functor.assoc` but that gives a "motive is type-incorrect"
    erw [limMap_π_assoc]
    dsimp

/-- The (limit) cone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed from the limit
of `F ⋙ evaluation R X` for all `X`. -/
@[simps]
noncomputable def limitCone : Cone F where
  pt := limitPresheafOfModules F
  π :=
    { app := fun j ↦
        { app := fun X ↦ limit.π (F ⋙ evaluation R X) j
          naturality := fun {X Y} f ↦ by
            dsimp
            simp only [assoc, preservesLimitIso_inv_π]
            apply limMap_π }
      naturality := fun {j j'} f ↦ by
        ext1 X
        simpa using (limit.w (F ⋙ evaluation R X) f).symm }

/-- The cone `limitCone F` is limit for any `F : J ⥤ PresheafOfModules.{v} R`. -/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

instance hasLimit : HasLimit F := ⟨_, isLimitLimitCone F⟩

noncomputable instance evaluation_preservesLimit (X : Cᵒᵖ) :
    PreservesLimit F (evaluation R X) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (limit.isLimit _)

noncomputable instance toPresheaf_preservesLimit :
    PreservesLimit F (toPresheaf R) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
    (Limits.evaluationJointlyReflectsLimits _
      (fun X => isLimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrp)
        (isLimitLimitCone F)))

end Limits

variable (R J)

section Small

variable [Small.{v} J]

instance hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{v} R) where

instance hasLimitsOfSize : HasLimitsOfSize.{v, v} (PresheafOfModules.{v} R) where

noncomputable instance evaluation_preservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (evaluation R X : PresheafOfModules.{v} R ⥤ _) where

noncomputable instance toPresheaf_preservesLimitsOfShape :
    PreservesLimitsOfShape J (toPresheaf.{v} R) where

end Small

section Finite

instance hasFiniteLimits : HasFiniteLimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance evaluation_preservesFiniteLimits (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where

noncomputable instance toPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (toPresheaf.{v} R) where

end Finite

end PresheafOfModules
