/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Limits.Opposites

/-!
# The opposite of an abelian category is abelian.
-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

variable (C : Type*) [Category C] [Abelian C]

instance : Abelian Cᵒᵖ := by
  -- Porting note: priorities of `Abelian.has_kernels` and `Abelian.has_cokernels` have
  -- been set to 90 in `Abelian.Basic` in order to prevent a timeout here
  exact {
    normalMonoOfMono := fun f => ⟨normalMonoOfNormalEpiUnop _ (normalEpiOfEpi f.unop)⟩
    normalEpiOfEpi := fun f => ⟨normalEpiOfNormalMonoUnop _ (normalMonoOfMono f.unop)⟩ }

section

variable {C}
variable {X Y : C} (f : X ⟶ Y) {A B : Cᵒᵖ} (g : A ⟶ B)

-- TODO: Generalize (this will work whenever f has a cokernel)
-- (The abelian case is probably sufficient for most applications.)
/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernelOpUnop : (kernel f.op).unop ≅ cokernel f where
  hom := (kernel.lift f.op (cokernel.π f).op <| by simp [← op_comp]).unop
  inv :=
    cokernel.desc f (kernel.ι f.op).unop <| by
      rw [← f.unop_op, ← unop_comp, f.unop_op]
      simp
  hom_inv_id := by
    rw [← unop_id, ← (cokernel.desc f _ _).unop_op, ← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

-- TODO: Generalize (this will work whenever f has a kernel)
-- (The abelian case is probably sufficient for most applications.)
/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernelOpUnop : (cokernel f.op).unop ≅ kernel f where
  hom :=
    kernel.lift f (cokernel.π f.op).unop <| by
      rw [← f.unop_op, ← unop_comp, f.unop_op]
      simp
  inv := (cokernel.desc f.op (kernel.ι f).op <| by simp [← op_comp]).unop
  hom_inv_id := by
    rw [← unop_id, ← (kernel.lift f _ _).unop_op, ← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps!]
def kernelUnopOp : Opposite.op (kernel g.unop) ≅ cokernel g :=
  (cokernelOpUnop g.unop).op

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps!]
def cokernelUnopOp : Opposite.op (cokernel g.unop) ≅ kernel g :=
  (kernelOpUnop g.unop).op

theorem cokernel.π_op :
    (cokernel.π f.op).unop =
      (cokernelOpUnop f).hom ≫ kernel.ι f ≫ eqToHom (Opposite.unop_op _).symm := by
  simp [cokernelOpUnop]

theorem kernel.ι_op :
    (kernel.ι f.op).unop = eqToHom (Opposite.unop_op _) ≫ cokernel.π f ≫ (kernelOpUnop f).inv := by
  simp [kernelOpUnop]

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps!]
def kernelOpOp : kernel f.op ≅ Opposite.op (cokernel f) :=
  (kernelOpUnop f).op.symm

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps!]
def cokernelOpOp : cokernel f.op ≅ Opposite.op (kernel f) :=
  (cokernelOpUnop f).op.symm

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps!]
def kernelUnopUnop : kernel g.unop ≅ (cokernel g).unop :=
  (kernelUnopOp g).unop.symm

theorem kernel.ι_unop :
    (kernel.ι g.unop).op = eqToHom (Opposite.op_unop _) ≫ cokernel.π g ≫ (kernelUnopOp g).inv := by
  simp

theorem cokernel.π_unop :
    (cokernel.π g.unop).op =
      (cokernelUnopOp g).hom ≫ kernel.ι g ≫ eqToHom (Opposite.op_unop _).symm := by
  simp

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps!]
def cokernelUnopUnop : cokernel g.unop ≅ (kernel g).unop :=
  (cokernelUnopOp g).unop.symm

/-- The opposite of the image of `g.unop` is the image of `g.` -/
def imageUnopOp : Opposite.op (image g.unop) ≅ image g :=
  (Abelian.imageIsoImage _).op ≪≫
    (cokernelOpOp _).symm ≪≫
      cokernelIsoOfEq (cokernel.π_unop _) ≪≫
        cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ Abelian.coimageIsoImage' _

/-- The opposite of the image of `f` is the image of `f.op`. -/
def imageOpOp : Opposite.op (image f) ≅ image f.op :=
  imageUnopOp f.op

/-- The image of `f.op` is the opposite of the image of `f`. -/
def imageOpUnop : (image f.op).unop ≅ image f :=
  (imageUnopOp f.op).unop

/-- The image of `g` is the opposite of the image of `g.unop.` -/
def imageUnopUnop : (image g).unop ≅ image g.unop :=
  (imageUnopOp g).unop

theorem image_ι_op_comp_imageUnopOp_hom :
    (image.ι g.unop).op ≫ (imageUnopOp g).hom = factorThruImage g := by
  simp only [imageUnopOp, Iso.trans, Iso.symm, Iso.op, cokernelOpOp_inv, cokernelEpiComp_hom,
    cokernelCompIsIso_hom, Abelian.coimageIsoImage'_hom, ← Category.assoc, ← op_comp]
  simp only [Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι, kernel.lift_ι,
    Quiver.Hom.op_unop, cokernelIsoOfEq_hom_comp_desc_assoc, cokernel.π_desc_assoc,
    cokernel.π_desc]
  simp only [eqToHom_refl]
  rw [IsIso.inv_id, Category.id_comp]

theorem imageUnopOp_hom_comp_image_ι :
    (imageUnopOp g).hom ≫ image.ι g = (factorThruImage g.unop).op := by
  simp only [← cancel_epi (image.ι g.unop).op, ← Category.assoc, image_ι_op_comp_imageUnopOp_hom,
    ← op_comp, image.fac, Quiver.Hom.op_unop]

theorem factorThruImage_comp_imageUnopOp_inv :
    factorThruImage g ≫ (imageUnopOp g).inv = (image.ι g.unop).op := by
  rw [Iso.comp_inv_eq, image_ι_op_comp_imageUnopOp_hom]

theorem imageUnopOp_inv_comp_op_factorThruImage :
    (imageUnopOp g).inv ≫ (factorThruImage g.unop).op = image.ι g := by
  rw [Iso.inv_comp_eq, imageUnopOp_hom_comp_image_ι]

end

end CategoryTheory

end
