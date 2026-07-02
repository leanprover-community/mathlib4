/-
Copyright (c) 2025 Yaël Dillies, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# (Co)kernels in functor categories
-/

@[expose] public section

namespace CategoryTheory.Limits
variable (J C : Type*) [Category* J] [Category* C] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/-- The kernel inclusion is itself a kernel in the functor category. -/
noncomputable def kerIsKernel [HasKernels C] :
    IsLimit (KernelFork.ofι (ker.ι C) (ker.condition C)) :=
  evaluationJointlyReflectsLimits _ fun f ↦ (KernelFork.isLimitMapConeEquiv ..).2 <|
    (kernelIsKernel f.hom).ofIsoLimit <| Fork.ext <| .refl _

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel projection is itself a cokernel in the functor category. -/
noncomputable def cokerIsCokernel [HasCokernels C] :
    IsColimit (CokernelCofork.ofπ (coker.π C) (coker.condition C)) :=
  evaluationJointlyReflectsColimits _ fun f ↦ (CokernelCofork.isColimitMapCoconeEquiv ..).2 <|
    (cokernelIsCokernel f.hom).ofIsoColimit <| Cofork.ext <| .refl _

variable {J C} {F₁ F₂ : J ⥤ C} (f : F₁ ⟶ F₂)

set_option backward.defeqAttrib.useBackward true in
lemma hasKernel_of_hasKernel_app [∀ j, HasKernel (f.app j)] : HasKernel f :=
  have (j : J) : HasLimit ((parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  functorCategoryHasLimit _

set_option backward.defeqAttrib.useBackward true in
lemma hasCokernel_of_hasCokernel_app [∀ j, HasCokernel (f.app j)] : HasCokernel f :=
  have (j : J) : HasColimit ((parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  functorCategoryHasColimit _

set_option backward.defeqAttrib.useBackward true in
lemma evaluation_preservesKernel_of_hasKernel_app [∀ j, HasKernel (f.app j)] (j : J) :
    PreservesLimit (parallelPair f 0) ((evaluation _ _).obj j) :=
  have (j : J) : HasLimit ((parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  preservesLimit_of_preserves_limit_cone
    (combinedIsLimit (F := parallelPair f 0)
      (fun j ↦ getLimitCone ((parallelPair f 0).flip.obj j)))
    (limit.isLimit _)

set_option backward.defeqAttrib.useBackward true in
lemma evaluation_preservesCokernel_of_hasCokernel_app [∀ j, HasCokernel (f.app j)] (j : J) :
    PreservesColimit (parallelPair f 0) ((evaluation _ _).obj j) :=
  have (j : J) : HasColimit ((parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  preservesColimit_of_preserves_colimit_cocone
    (combinedIsColimit (F := parallelPair f 0)
      (fun j ↦ getColimitCocone ((parallelPair f 0).flip.obj j)))
    (colimit.isColimit _)

end CategoryTheory.Limits
