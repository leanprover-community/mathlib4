/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Preservation of coimage-image comparisons

If a functor preserves kernels and cokernels, then it preserves abelian images, abelian coimages
and coimage-image comparisons.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory.Abelian

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable {X Y : C} (f : X ⟶ Y)

section Images

variable [HasCokernel f] [HasKernel (cokernel.π f)] [PreservesColimit (parallelPair f 0) F]
  [PreservesLimit (parallelPair (cokernel.π f) 0) F] [HasCokernel (F.map f)]
  [HasKernel (cokernel.π (F.map f))]

/-- If a functor preserves kernels and cokernels, it preserves abelian images. -/
def PreservesImage.iso : F.obj (Abelian.image f) ≅ Abelian.image (F.map f) :=
  PreservesKernel.iso F _ ≪≫ kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso F _) (by simp)

@[reassoc (attr := simp)]
theorem PreservesImage.iso_hom_ι :
    (PreservesImage.iso F f).hom ≫ Abelian.image.ι (F.map f) = F.map (Abelian.image.ι f) := by
  simp [iso]

@[reassoc (attr := simp)]
theorem PreservesImage.factorThruImage_iso_hom :
    F.map (Abelian.factorThruImage f) ≫ (PreservesImage.iso F f).hom =
      Abelian.factorThruImage (F.map f) := by
  ext; simp [iso]

@[reassoc (attr := simp)]
theorem PreservesImage.iso_inv_ι :
    (PreservesImage.iso F f).inv ≫ F.map (Abelian.image.ι f) = Abelian.image.ι (F.map f) := by
  simp [iso]

@[reassoc (attr := simp)]
theorem PreservesImage.factorThruImage_iso_inv :
    Abelian.factorThruImage (F.map f) ≫ (PreservesImage.iso F f).inv =
      F.map (Abelian.factorThruImage f) := by
  simp [Iso.comp_inv_eq]

end Images

section Coimages

variable [HasKernel f] [HasCokernel (kernel.ι f)] [PreservesLimit (parallelPair f 0) F]
  [PreservesColimit (parallelPair (kernel.ι f) 0) F] [HasKernel (F.map f)]
  [HasCokernel (kernel.ι (F.map f))]

/-- If a functor preserves kernels and cokernels, it preserves abelian coimages. -/
def PreservesCoimage.iso : F.obj (Abelian.coimage f) ≅ Abelian.coimage (F.map f) :=
  PreservesCokernel.iso F _ ≪≫ cokernel.mapIso _ _ (PreservesKernel.iso F _) (Iso.refl _) (by simp)

@[reassoc (attr := simp)]
theorem PreservesCoimage.iso_hom_π :
    F.map (Abelian.coimage.π f) ≫ (PreservesCoimage.iso F f).hom = Abelian.coimage.π (F.map f) := by
  simp [iso]

@[reassoc (attr := simp)]
theorem PreservesCoimage.factorThruCoimage_iso_inv :
    (PreservesCoimage.iso F f).inv ≫ F.map (Abelian.factorThruCoimage f)  =
      Abelian.factorThruCoimage (F.map f) := by
  ext; simp [iso]

@[reassoc (attr := simp)]
theorem PreservesCoimage.factorThruCoimage_iso_hom :
    (PreservesCoimage.iso F f).hom ≫ Abelian.factorThruCoimage (F.map f) =
      F.map (Abelian.factorThruCoimage f) := by
  simp [← Iso.eq_inv_comp]

@[reassoc (attr := simp)]
theorem PreservesCoimage.iso_inv_π :
    Abelian.coimage.π (F.map f) ≫ (PreservesCoimage.iso F f).inv = F.map (Abelian.coimage.π f) := by
  simp [Iso.comp_inv_eq]

end Coimages

variable [HasKernel f] [HasCokernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]
  [PreservesLimit (parallelPair f 0) F] [PreservesColimit (parallelPair f 0) F]
  [PreservesLimit (parallelPair (cokernel.π f) 0) F]
  [PreservesColimit (parallelPair (kernel.ι f) 0) F]
  [HasKernel (cokernel.π (F.map f))] [HasCokernel (kernel.ι (F.map f))]

theorem PreservesCoimage.hom_coimageImageComparison :
    (PreservesCoimage.iso F f).hom ≫ coimageImageComparison (F.map f) =
      F.map (coimageImageComparison f) ≫ (PreservesImage.iso F f).hom := by
  simp [← Functor.map_comp, ← Iso.eq_inv_comp, ← cancel_epi (Abelian.coimage.π (F.map f)),
    ← cancel_mono (Abelian.image.ι (F.map f))]

/-- If a functor preserves kernels and cokernels, it preserves coimage-image comparisons. -/
@[simps!]
def PreservesCoimageImageComparison.iso :
    Arrow.mk (F.map (coimageImageComparison f)) ≅ Arrow.mk (coimageImageComparison (F.map f)) :=
  Arrow.isoMk' _ _ (PreservesCoimage.iso F f) (PreservesImage.iso F f)
    (PreservesCoimage.hom_coimageImageComparison F f)

end CategoryTheory.Abelian
