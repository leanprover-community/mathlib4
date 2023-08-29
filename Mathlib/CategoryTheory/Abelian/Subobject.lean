/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Basic

#align_import category_theory.abelian.subobject from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Equivalence between subobjects and quotients in an abelian category

-/


open CategoryTheory CategoryTheory.Limits Opposite

universe v u

noncomputable section

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C]

/-- In an abelian category, the subobjects and quotient objects of an object `X` are
    order-isomorphic via taking kernels and cokernels.
    Implemented here using subobjects in the opposite category,
    since mathlib does not have a notion of quotient objects at the time of writing. -/
@[simps!]
def subobjectIsoSubobjectOp [Abelian C] (X : C) : Subobject X ≃o (Subobject (op X))ᵒᵈ := by
  refine' OrderIso.ofHomInv (cokernelOrderHom X) (kernelOrderHom X) _ _
  -- ⊢ OrderHom.comp ↑(cokernelOrderHom X) ↑(kernelOrderHom X) = OrderHom.id
  · change (cokernelOrderHom X).comp (kernelOrderHom X) = _
    -- ⊢ OrderHom.comp (cokernelOrderHom X) (kernelOrderHom X) = OrderHom.id
    refine' OrderHom.ext _ _ (funext (Subobject.ind _ _))
    -- ⊢ ∀ ⦃A : Cᵒᵖ⦄ (f : A ⟶ op X) [inst : Mono f], ↑(OrderHom.comp (cokernelOrderHo …
    intro A f hf
    -- ⊢ ↑(OrderHom.comp (cokernelOrderHom X) (kernelOrderHom X)) (Subobject.mk f) =  …
    dsimp only [OrderHom.comp_coe, Function.comp_apply, kernelOrderHom_coe, Subobject.lift_mk,
      cokernelOrderHom_coe, OrderHom.id_coe, id.def]
    refine' Subobject.mk_eq_mk_of_comm _ _ ⟨_, _, Quiver.Hom.unop_inj _, Quiver.Hom.unop_inj _⟩ _
    · exact (Abelian.epiDesc f.unop _ (cokernel.condition (kernel.ι f.unop))).op
      -- 🎉 no goals
    · exact (cokernel.desc _ _ (kernel.condition f.unop)).op
      -- 🎉 no goals
    · rw [← cancel_epi (cokernel.π (kernel.ι f.unop))]
      -- ⊢ cokernel.π (kernel.ι f.unop) ≫ ((epiDesc f.unop (cokernel.π (kernel.ι f.unop …
      simp only [unop_comp, Quiver.Hom.unop_op, unop_id_op, cokernel.π_desc_assoc,
        comp_epiDesc, Category.comp_id]
    · simp only [← cancel_epi f.unop, unop_comp, Quiver.Hom.unop_op, unop_id, comp_epiDesc_assoc,
        cokernel.π_desc, Category.comp_id]
    · exact Quiver.Hom.unop_inj (by simp only [unop_comp, Quiver.Hom.unop_op, comp_epiDesc])
      -- 🎉 no goals
  · change (kernelOrderHom X).comp (cokernelOrderHom X) = _
    -- ⊢ OrderHom.comp (kernelOrderHom X) (cokernelOrderHom X) = OrderHom.id
    refine' OrderHom.ext _ _ (funext (Subobject.ind _ _))
    -- ⊢ ∀ ⦃A : C⦄ (f : A ⟶ X) [inst : Mono f], ↑(OrderHom.comp (kernelOrderHom X) (c …
    intro A f hf
    -- ⊢ ↑(OrderHom.comp (kernelOrderHom X) (cokernelOrderHom X)) (Subobject.mk f) =  …
    dsimp only [OrderHom.comp_coe, Function.comp_apply, cokernelOrderHom_coe, Subobject.lift_mk,
      kernelOrderHom_coe, OrderHom.id_coe, id.def, unop_op, Quiver.Hom.unop_op]
    refine' Subobject.mk_eq_mk_of_comm _ _ ⟨_, _, _, _⟩ _
    · exact Abelian.monoLift f _ (kernel.condition (cokernel.π f))
      -- 🎉 no goals
    · exact kernel.lift _ _ (cokernel.condition f)
      -- 🎉 no goals
    · simp only [← cancel_mono (kernel.ι (cokernel.π f)), Category.assoc, image.fac, monoLift_comp,
        Category.id_comp]
    · simp only [← cancel_mono f, Category.assoc, monoLift_comp, image.fac, Category.id_comp]
      -- 🎉 no goals
    · simp only [monoLift_comp]
      -- 🎉 no goals
#align category_theory.abelian.subobject_iso_subobject_op CategoryTheory.Abelian.subobjectIsoSubobjectOp

/-- A well-powered abelian category is also well-copowered. -/
instance wellPowered_opposite [Abelian C] [WellPowered C] : WellPowered Cᵒᵖ
    where subobject_small X :=
    (small_congr (subobjectIsoSubobjectOp (unop X)).toEquiv).1 inferInstance
#align category_theory.abelian.well_powered_opposite CategoryTheory.Abelian.wellPowered_opposite

end CategoryTheory.Abelian
