/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Colimits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
colimits exist in the category `PresheafOfModules R`.

-/

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Limits

variable [∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), PreservesColimit (F ⋙ evaluation R Y)
  (ModuleCat.restrictScalars (R.map f))]

/-- A cocone in the category `PresheafOfModules R` is colimit if it is so after the application
of the functors `evaluation R X` for all `X`. -/
def evaluationJointlyReflectsColimits (c : Cocone F)
    (hc : ∀ (X : Cᵒᵖ), IsColimit ((evaluation R X).mapCocone c)) : IsColimit c where
  desc s := Hom.mk'' (fun X => (hc X).desc ((evaluation R X).mapCocone s)) (fun X Y f => by
    apply (hc X).hom_ext
    intro j
    erw [(hc X).fac_assoc ((evaluation R X).mapCocone s) j, ← restrictionApp_naturality_assoc]
    rw [← Functor.map_comp]
    erw [(hc Y).fac ((evaluation R Y).mapCocone s), restrictionApp_naturality]
    rfl)
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCocone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCocone s)
    intro j
    dsimp
    rw [← hm]
    rfl

variable [∀ X, HasColimit (F ⋙ evaluation R X)]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasColimit (F ⋙ evaluation R Y ⋙ (ModuleCat.restrictScalars (R.map f))) :=
  ⟨_, isColimitOfPreserves (ModuleCat.restrictScalars (R.map f))
    (colimit.isColimit (F ⋙ evaluation R Y))⟩

/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the `BundledCorePresheafOfModules R` which
corresponds to the presheaf of modules which sends `X` to the colimit of `F ⋙ evaluation R X`. -/
@[simps]
noncomputable def colimitBundledCore : BundledCorePresheafOfModules R where
  obj X := colimit (F ⋙ evaluation R X)
  map {X Y} f := colimMap (whiskerLeft F (restriction R f)) ≫
    (preservesColimitIso (ModuleCat.restrictScalars (R.map f)) (F ⋙ evaluation R Y)).inv
  map_id := sorry
  map_comp := sorry

/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the canonical map
`F.obj j ⟶ (colimitBundledCore F).toPresheafOfModules` for all `j : J`. -/
noncomputable def colimitCoconeιApp (j : J) :
    F.obj j ⟶ (colimitBundledCore F).toPresheafOfModules :=
  PresheafOfModules.Hom.mk'' (fun X => colimit.ι (F ⋙ evaluation R X) j) (fun X Y f => by
    dsimp
    erw [colimit.ι_desc_assoc, assoc, ← ι_preservesColimitsIso_inv]
    rfl)

@[reassoc (attr := simp)]
lemma colimitCoconeιApp_naturality {i j : J} (f : i ⟶ j) :
    F.map f ≫ colimitCoconeιApp F j = colimitCoconeιApp F i := by
  ext1 X
  exact colimit.w (F ⋙ evaluation R X) f

/-- The (colimit) cocone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed from
the colimit of `F ⋙ evaluation R X` for all `X`. -/
@[simps]
noncomputable def colimitCocone : Cocone F where
  pt := (colimitBundledCore F).toPresheafOfModules
  ι := { app := colimitCoconeιApp F }

/-- The cone `colimitCocone F` is colimit for any `F : J ⥤ PresheafOfModules.{v} R`. -/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  evaluationJointlyReflectsColimits _ _ (fun _ => colimit.isColimit _)

instance hasColimit : HasColimit F := ⟨_, isColimitColimitCocone F⟩

noncomputable instance evaluationPreservesColimit (X : Cᵒᵖ) :
    PreservesColimit F (evaluation R X) :=
  preservesColimitOfPreservesColimitCocone (isColimitColimitCocone F) (colimit.isColimit _)

variable [∀ X, PreservesColimit F
  (evaluation R X ⋙ forget₂ (ModuleCat (R.obj X)) AddCommGroupCat)]

noncomputable instance toPresheafPreservesColimit :
    PreservesColimit F (toPresheaf R) :=
  preservesColimitOfPreservesColimitCocone (isColimitColimitCocone F)
    (Limits.evaluationJointlyReflectsColimits _
      (fun X => isColimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGroupCat)
        (isColimitColimitCocone F)))

end Limits

variable (R J)

section HasColimitsOfShape

variable [HasColimitsOfShape J AddCommGroupCat.{v}]

instance hasColimitsOfShape : HasColimitsOfShape J (PresheafOfModules.{v} R) where

noncomputable instance evaluationPreservesColimitsOfShape (X : Cᵒᵖ) :
    PreservesColimitsOfShape J (evaluation R X : PresheafOfModules.{v} R ⥤ _) where

noncomputable instance toPresheafPreservesColimitsOfShape :
    PreservesColimitsOfShape J (toPresheaf.{v} R) where

end HasColimitsOfShape

namespace Finite

instance hasFiniteColimits : HasFiniteColimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance evaluationPreservesFiniteColimits (X : Cᵒᵖ) :
    PreservesFiniteColimits (evaluation.{v} R X) where

noncomputable instance toPresheafPreservesFiniteColimits :
    PreservesFiniteColimits (toPresheaf R) where

end Finite

end PresheafOfModules
