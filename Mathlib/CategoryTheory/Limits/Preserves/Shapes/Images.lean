/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

#align_import category_theory.limits.preserves.shapes.images from "leanprover-community/mathlib"@"fc78e3c190c72a109699385da6be2725e88df841"

/-!
# Preserving images

In this file, we show that if a functor preserves span and cospan, then it preserves images.
-/


noncomputable section

namespace CategoryTheory

namespace PreservesImage

open CategoryTheory

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

variable [HasEqualizers A] [HasImages A]

variable [StrongEpiCategory B] [HasImages B]

variable (L : A ⥤ B)

variable [∀ {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) L]

variable [∀ {X Y Z : A} (f : X ⟶ Y) (g : X ⟶ Z), PreservesColimit (span f g) L]

/-- If a functor preserves span and cospan, then it preserves images.
-/
@[simps!]
def iso {X Y : A} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
  let aux1 : StrongEpiMonoFactorisation (L.map f) :=
    { I := L.obj (Limits.image f)
      m := L.map <| Limits.image.ι _
      m_mono := preserves_mono_of_preservesLimit _ _
      e := L.map <| factorThruImage _
      e_strong_epi := @strongEpi_of_epi B _ _ _ _ _ (preserves_epi_of_preservesColimit L _)
      fac := by rw [← L.map_comp, Limits.image.fac] }
                -- 🎉 no goals
  IsImage.isoExt (Image.isImage (L.map f)) aux1.toMonoIsImage
#align category_theory.preserves_image.iso CategoryTheory.PreservesImage.iso

@[reassoc]
theorem factorThruImage_comp_hom {X Y : A} (f : X ⟶ Y) :
    factorThruImage (L.map f) ≫ (iso L f).hom = L.map (factorThruImage f) := by simp
                                                                                -- 🎉 no goals
#align category_theory.preserves_image.factor_thru_image_comp_hom CategoryTheory.PreservesImage.factorThruImage_comp_hom

@[reassoc]
theorem hom_comp_map_image_ι {X Y : A} (f : X ⟶ Y) :
    (iso L f).hom ≫ L.map (image.ι f) = image.ι (L.map f) := by rw [iso_hom, image.lift_fac]
                                                                -- 🎉 no goals
#align category_theory.preserves_image.hom_comp_map_image_ι CategoryTheory.PreservesImage.hom_comp_map_image_ι

@[reassoc]
theorem inv_comp_image_ι_map {X Y : A} (f : X ⟶ Y) :
    (iso L f).inv ≫ image.ι (L.map f) = L.map (image.ι f) := by simp
                                                                -- 🎉 no goals
#align category_theory.preserves_image.inv_comp_image_ι_map CategoryTheory.PreservesImage.inv_comp_image_ι_map

end PreservesImage

end CategoryTheory
