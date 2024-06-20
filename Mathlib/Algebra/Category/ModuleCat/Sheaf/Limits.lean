/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.Limits

/-! # Limits in categories of sheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `SheafOfModules R`.

## TODO
* do the same for colimits (which requires constructing
the associated sheaf of modules functor)

-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Category Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ RingCat.{u}}
  {F : D ⥤ PresheafOfModules.{v} R}
  [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]
  {c : Cone F} (hc : IsLimit c)
  (hF : ∀ j, Presheaf.IsSheaf J (F.obj j).presheaf)
  [HasLimitsOfShape D AddCommGrp.{v}]

lemma isSheaf_of_isLimit : Presheaf.IsSheaf J (c.pt.presheaf) := by
  let G : D ⥤ Sheaf J AddCommGrp.{v} :=
    { obj := fun j => ⟨(F.obj j).presheaf, hF j⟩
      map := fun φ => ⟨(PresheafOfModules.toPresheaf R).map (F.map φ)⟩ }
  exact Sheaf.isSheaf_of_isLimit G _ (isLimitOfPreserves (toPresheaf R) hc)

end PresheafOfModules

namespace SheafOfModules

variable {R : Sheaf J RingCat.{u}}

section Limits

variable (F : D ⥤ SheafOfModules.{v} R)
  [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ CategoryTheory.forget _).sections]
  [HasLimitsOfShape D AddCommGrp.{v}]

instance (X : Cᵒᵖ) : Small.{v} (((F ⋙ forget _) ⋙ PresheafOfModules.evaluation _ X) ⋙
    CategoryTheory.forget _).sections := by
  change Small.{v} ((F ⋙ evaluation R X) ⋙ CategoryTheory.forget _).sections
  infer_instance

noncomputable instance createsLimit : CreatesLimit F (forget _) :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit (F ⋙ forget _))
    (mk (limit (F ⋙ forget _))
      (PresheafOfModules.isSheaf_of_isLimit (limit.isLimit (F ⋙ forget _))
        (fun j => (F.obj j).isSheaf))) (Iso.refl _)

instance hasLimit : HasLimit F := hasLimit_of_created F (forget _)

noncomputable instance evaluationPreservesLimit (X : Cᵒᵖ) :
    PreservesLimit F (evaluation R X) := by
  dsimp [evaluation]
  infer_instance

end Limits

variable (R D)

section Small

variable [Small.{v} D]

instance hasLimitsOfShape : HasLimitsOfShape D (SheafOfModules.{v} R) where

noncomputable instance evaluationPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape D (evaluation R X : SheafOfModules.{v} R ⥤ _) where

noncomputable instance forgetPreservesLimitsOfShape :
    PreservesLimitsOfShape D (forget.{v} R) where

end Small

namespace Finite

instance hasFiniteLimits : HasFiniteLimits (SheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance evaluationPreservesFiniteLimits (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where

noncomputable instance forgetPreservesFiniteLimits :
    PreservesFiniteLimits (forget.{v} R) where

end Finite

instance hasLimitsOfSize : HasLimitsOfSize.{v₂, v} (SheafOfModules.{v} R) where

noncomputable instance evaluationPreservesLimitsOfSize (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{v₂, v} (evaluation R X : SheafOfModules.{v} R ⥤ _) where

noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v₂, v} (forget.{v} R) where

noncomputable instance :
     PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _) :=
  compPreservesFiniteLimits (SheafOfModules.forget.{v} R) (PresheafOfModules.toPresheaf R.val)

noncomputable instance : PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R) :=
  preservesFiniteLimitsOfReflectsOfPreserves _ (sheafToPresheaf _ _)

end SheafOfModules
