/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

#align_import category_theory.abelian.functor_category from "leanprover-community/mathlib"@"8abfb3ba5e211d8376b855dab5d67f9eba9e0774"

/-!
# If `D` is abelian, then the functor category `C ⥤ D` is also abelian.

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

namespace Abelian

section

universe z w v u

-- porting note: removed restrictions on universes

variable {C : Type u} [Category.{v} C]

variable {D : Type w} [Category.{z} D] [Abelian D]

namespace FunctorCategory

variable {F G : C ⥤ D} (α : F ⟶ G) (X : C)

/-- The abelian coimage in a functor category can be calculated componentwise. -/
@[simps!]
def coimageObjIso : (Abelian.coimage α).obj X ≅ Abelian.coimage (α.app X) :=
  PreservesCokernel.iso ((evaluation C D).obj X) _ ≪≫
    cokernel.mapIso _ _ (PreservesKernel.iso ((evaluation C D).obj X) _) (Iso.refl _)
      (by
        dsimp
        -- ⊢ NatTrans.app (kernel.ι α) X ≫ 𝟙 (F.obj X) = (PreservesKernel.iso ((evaluatio …
        simp only [Category.comp_id, PreservesKernel.iso_hom]
        -- ⊢ NatTrans.app (kernel.ι α) X = kernelComparison α ((evaluation C D).obj X) ≫  …
        exact (kernelComparison_comp_ι _ ((evaluation C D).obj X)).symm)
        -- 🎉 no goals
#align category_theory.abelian.functor_category.coimage_obj_iso CategoryTheory.Abelian.FunctorCategory.coimageObjIso

/-- The abelian image in a functor category can be calculated componentwise. -/
@[simps!]
def imageObjIso : (Abelian.image α).obj X ≅ Abelian.image (α.app X) :=
  PreservesKernel.iso ((evaluation C D).obj X) _ ≪≫
    kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso ((evaluation C D).obj X) _)
      (by
        apply (cancel_mono (PreservesCokernel.iso ((evaluation C D).obj X) α).inv).1
        -- ⊢ (((evaluation C D).obj X).map (cokernel.π α) ≫ (PreservesCokernel.iso ((eval …
        simp only [Category.assoc, Iso.hom_inv_id]
        -- ⊢ ((evaluation C D).obj X).map (cokernel.π α) ≫ 𝟙 (((evaluation C D).obj X).ob …
        dsimp
        -- ⊢ NatTrans.app (cokernel.π α) X ≫ 𝟙 ((cokernel α).obj X) = 𝟙 (G.obj X) ≫ coker …
        simp only [PreservesCokernel.iso_inv, Category.id_comp, Category.comp_id]
        -- ⊢ NatTrans.app (cokernel.π α) X = cokernel.π (NatTrans.app α X) ≫ cokernelComp …
        exact (π_comp_cokernelComparison _ ((evaluation C D).obj X)).symm)
        -- 🎉 no goals
#align category_theory.abelian.functor_category.image_obj_iso CategoryTheory.Abelian.FunctorCategory.imageObjIso

theorem coimageImageComparison_app :
    coimageImageComparison (α.app X) =
      (coimageObjIso α X).inv ≫ (coimageImageComparison α).app X ≫ (imageObjIso α X).hom := by
  ext
  -- ⊢ (coequalizer.π (kernel.ι (NatTrans.app α X)) 0 ≫ coimageImageComparison (Nat …
  dsimp
  -- ⊢ (cokernel.π (kernel.ι (NatTrans.app α X)) ≫ coimageImageComparison (NatTrans …
  dsimp [imageObjIso, coimageObjIso, cokernel.map]
  -- ⊢ (cokernel.π (kernel.ι (NatTrans.app α X)) ≫ coimageImageComparison (NatTrans …
  simp only [coimage_image_factorisation, PreservesKernel.iso_hom, Category.assoc,
    kernel.lift_ι, Category.comp_id, PreservesCokernel.iso_inv,
    cokernel.π_desc_assoc, Category.id_comp]
  erw [kernelComparison_comp_ι _ ((evaluation C D).obj X),
    π_comp_cokernelComparison_assoc _ ((evaluation C D).obj X)]
  conv_lhs => rw [← coimage_image_factorisation α]
  -- 🎉 no goals
#align category_theory.abelian.functor_category.coimage_image_comparison_app CategoryTheory.Abelian.FunctorCategory.coimageImageComparison_app

theorem coimageImageComparison_app' :
    (coimageImageComparison α).app X =
      (coimageObjIso α X).hom ≫ coimageImageComparison (α.app X) ≫ (imageObjIso α X).inv := by
  simp only [coimageImageComparison_app, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.assoc,
    Category.comp_id]
#align category_theory.abelian.functor_category.coimage_image_comparison_app' CategoryTheory.Abelian.FunctorCategory.coimageImageComparison_app'

instance functor_category_isIso_coimageImageComparison :
    IsIso (Abelian.coimageImageComparison α) := by
  have : ∀ X : C, IsIso ((Abelian.coimageImageComparison α).app X) := by
    intros
    rw [coimageImageComparison_app']
    infer_instance
  apply NatIso.isIso_of_isIso_app
  -- 🎉 no goals
#align category_theory.abelian.functor_category.functor_category_is_iso_coimage_image_comparison CategoryTheory.Abelian.FunctorCategory.functor_category_isIso_coimageImageComparison

end FunctorCategory

noncomputable instance functorCategoryAbelian : Abelian (C ⥤ D) :=
  let _ : HasKernels (C ⥤ D) := inferInstance
  let _ : HasCokernels (C ⥤ D) := inferInstance
  Abelian.ofCoimageImageComparisonIsIso
#align category_theory.abelian.functor_category_abelian CategoryTheory.Abelian.functorCategoryAbelian

end

--porting note: the following section should be unnecessary because there are no longer
--any universe restrictions for `functorCategoryAbelian`
--
--section
--
--universe u
--
--variable {C : Type u} [SmallCategory C]
--
--variable {D : Type (u + 1)} [LargeCategory D] [Abelian D]
--
--/-- A variant with specialized universes for a common case. -/
--noncomputable instance functorCategoryAbelian' : Abelian (C ⥤ D) :=
--  Abelian.functorCategoryAbelian.{u, u + 1, u, u}
--#align category_theory.abelian.functor_category_abelian' CategoryTheory.Abelian.functorCategoryAbelian'
--
--end

end Abelian

end CategoryTheory
