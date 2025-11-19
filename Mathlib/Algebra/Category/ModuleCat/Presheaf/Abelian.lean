/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The category of presheaves of modules is abelian

-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

noncomputable instance : IsNormalEpiCategory (PresheafOfModules.{v} R) where
  normalEpiOfEpi p _ := ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (evaluationJointlyReflectsColimits _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩

noncomputable instance : IsNormalMonoCategory (PresheafOfModules.{v} R) where
  normalMonoOfMono i _ := ⟨NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (evaluationJointlyReflectsLimits _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩

noncomputable instance : Abelian (PresheafOfModules.{v} R) where

end PresheafOfModules
