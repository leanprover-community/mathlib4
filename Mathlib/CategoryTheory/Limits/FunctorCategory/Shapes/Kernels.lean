/-
Copyright (c) 2025 Yaël Dillies, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# (Co)kernels in functor categories
-/

@[expose] public section

namespace CategoryTheory.Limits
variable (J C : Type*) [Category* J] [Category* C] [HasZeroMorphisms C]

/-- The kernel inclusion is itself a kernel in the functor category. -/
noncomputable def kerIsKernel [HasKernels C] :
    IsLimit (KernelFork.ofι (ker.ι C) (ker.condition C)) :=
  evaluationJointlyReflectsLimits _ fun f ↦ (KernelFork.isLimitMapConeEquiv ..).invFun <|
    (kernelIsKernel f.hom).ofIsoLimit <| Fork.ext <| .refl _

/-- The cokernel projection is itself a cokernel in the functor category. -/
noncomputable def cokerIsCokernel [HasCokernels C] :
    IsColimit (CokernelCofork.ofπ (coker.π C) (coker.condition C)) :=
  evaluationJointlyReflectsColimits _ fun f ↦ (CokernelCofork.isColimitMapCoconeEquiv ..).invFun <|
    (cokernelIsCokernel f.hom).ofIsoColimit <| Cofork.ext <| .refl _

variable {J C} {F₁ F₂ : J ⥤ C} (f : F₁ ⟶ F₂)

lemma hasKernel_of_hasKernel_app [∀ j, HasKernel (f.app j)] : HasKernel f :=
  have (j : J) : HasLimit ((parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  functorCategoryHasLimit _

lemma hasCokernel_of_hasCokernel_app [∀ j, HasCokernel (f.app j)] : HasCokernel f :=
  have (j : J) : HasColimit ((parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  functorCategoryHasColimit _

instance [HasKernels C] : HasKernels (J ⥤ C) where
  has_limit _ := hasKernel_of_hasKernel_app _

instance [HasCokernels C] : HasCokernels (J ⥤ C) where
  has_colimit _ := hasCokernel_of_hasCokernel_app _

lemma evaluation_preservesLimit_of_hasKernel_app [∀ j, HasKernel (f.app j)] (j : J) :
    PreservesLimit (parallelPair f 0) ((evaluation _ _).obj j) :=
  have (j : J) : HasLimit ((parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  preservesLimit_of_preserves_limit_cone
    (combinedIsLimit (F := parallelPair f 0)
      (fun j ↦ getLimitCone ((parallelPair f 0).flip.obj j)))
    (limit.isLimit _)

lemma evaluation_preservesColimit_of_hasCokernel_app [∀ j, HasCokernel (f.app j)] (j : J) :
    PreservesColimit (parallelPair f 0) ((evaluation _ _).obj j) :=
  have (j : J) : HasColimit ((parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  preservesColimit_of_preserves_colimit_cocone
    (combinedIsColimit (F := parallelPair f 0)
      (fun j ↦ getColimitCocone ((parallelPair f 0).flip.obj j)))
    (colimit.isColimit _)

section

variable [HasCokernel f] [∀ j, HasCokernel (f.app j)]

@[no_expose]
noncomputable def cokernelObjIso (j : J) : (cokernel f).obj j ≅ cokernel (f.app j) :=
  haveI := evaluation_preservesColimit_of_hasCokernel_app f j
  (IsColimit.coconePointUniqueUpToIso
    (CokernelCofork.mapIsColimit _ (cokernelIsCokernel f) ((evaluation _ _).obj j))
    (cokernelIsCokernel (f.app j)) :)

@[reassoc (attr := simp)]
lemma π_cokernelObjIso_hom (j : J) :
    (cokernel.π f).app j ≫ (cokernelObjIso f j).hom = cokernel.π (f.app j) :=
  have := evaluation_preservesColimit_of_hasCokernel_app f j
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (CokernelCofork.mapIsColimit _ (cokernelIsCokernel f) ((evaluation _ _).obj j))
      (cokernelIsCokernel (f.app j)) .one

@[simps!]
noncomputable def cokernelπAppArrowIso (j : J) :
    Arrow.mk ((cokernel.π f).app j) ≅ Arrow.mk (cokernel.π (f.app j)) :=
  Arrow.isoMk (Iso.refl _) (cokernelObjIso f j)

instance (j : J) : Epi ((cokernel.π f).app j) :=
  ((MorphismProperty.epimorphisms _).arrow_mk_iso_iff
    (cokernelπAppArrowIso f j)).2 inferInstance

@[reassoc (attr := simp)]
lemma cokernelObjIso_hom_cokernel_map {i j : J} (g : i ⟶ j) :
    (cokernelObjIso f i).hom ≫
      cokernel.map (f.app i) (f.app j) (F₁.map g) (F₂.map g) (by simp) =
    (cokernel f).map g ≫ (cokernelObjIso f j).hom := by
  simp [← cancel_epi ((cokernel.π f).app i), ← NatTrans.naturality_assoc]

noncomputable def cokernelMapArrowIso {i j : J} (g : i ⟶ j) :
    Arrow.mk ((cokernel f).map g) ≅
      Arrow.mk (cokernel.map (f.app i) (f.app j) (F₁.map g) (F₂.map g) (by simp)) :=
  Arrow.isoMk (cokernelObjIso f i) (cokernelObjIso f j)

end

end CategoryTheory.Limits
