/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Equivalence between subobjects and quotients in an abelian category

-/


open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Abelian

/-- In an abelian category, the subobjects and quotient objects of an object `X` are
    order-isomorphic via taking kernels and cokernels.
    Implemented here using subobjects in the opposite category,
    since mathlib does not have a notion of quotient objects at the time of writing. -/
@[simps!]
def subobjectIsoSubobjectOp (X : C) : Subobject X ≃o (Subobject (op X))ᵒᵈ := by
  refine OrderIso.ofHomInv (cokernelOrderHom X) (kernelOrderHom X) ?_ ?_
  · change (cokernelOrderHom X).comp (kernelOrderHom X) = _
    refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))
    intro A f hf
    dsimp only [OrderHom.comp_coe, Function.comp_apply, kernelOrderHom_coe, Subobject.lift_mk,
      cokernelOrderHom_coe, OrderHom.id_coe, id]
    refine Subobject.mk_eq_mk_of_comm _ _
        ⟨?_, ?_, Quiver.Hom.unop_inj ?_, Quiver.Hom.unop_inj ?_⟩ ?_
    · exact (Abelian.epiDesc f.unop _ (cokernel.condition (kernel.ι f.unop))).op
    · exact (cokernel.desc _ _ (kernel.condition f.unop)).op
    · rw [← cancel_epi (cokernel.π (kernel.ι f.unop))]
      simp only [unop_comp, Quiver.Hom.unop_op, unop_id_op, cokernel.π_desc_assoc,
        comp_epiDesc, Category.comp_id]
    · simp only [← cancel_epi f.unop, unop_comp, Quiver.Hom.unop_op, unop_id, comp_epiDesc_assoc,
        cokernel.π_desc, Category.comp_id]
    · exact Quiver.Hom.unop_inj (by simp only [unop_comp, Quiver.Hom.unop_op, comp_epiDesc])
  · change (kernelOrderHom X).comp (cokernelOrderHom X) = _
    refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))
    intro A f hf
    dsimp only [OrderHom.comp_coe, Function.comp_apply, cokernelOrderHom_coe, Subobject.lift_mk,
      kernelOrderHom_coe, OrderHom.id_coe, id, unop_op, Quiver.Hom.unop_op]
    refine Subobject.mk_eq_mk_of_comm _ _ ⟨?_, ?_, ?_, ?_⟩ ?_
    · exact Abelian.monoLift f _ (kernel.condition (cokernel.π f))
    · exact kernel.lift _ _ (cokernel.condition f)
    · simp only [← cancel_mono (kernel.ι (cokernel.π f)), Category.assoc, image.fac, monoLift_comp,
        Category.id_comp]
    · simp only [← cancel_mono f, Category.assoc, monoLift_comp, image.fac, Category.id_comp]
    · simp only [monoLift_comp]

/-- A well-powered abelian category is also well-copowered. -/
instance wellPowered_opposite [LocallySmall.{w} C] [WellPowered.{w} C] :
    WellPowered.{w} Cᵒᵖ where
  subobject_small X :=
    (small_congr (subobjectIsoSubobjectOp (unop X)).toEquiv).1 inferInstance

end Abelian

-- to be moved
section

variable {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : kernel.ι f ≫ g = 0)

def image.desc : image f ⟶ Z :=
  (Abelian.imageIsoImage f).inv ≫ (Abelian.coimageIsoImage f).inv ≫
    (cokernel.desc _ g w)

@[reassoc (attr := simp)]
lemma image.factorThruImage_desc : factorThruImage f ≫ desc f g w = g := by
  simp only [desc, IsImage.isoExt_inv, image.isImage_lift, asIso_inv, image.fac_lift_assoc,
    Abelian.imageStrongEpiMonoFactorisation_I, Abelian.imageStrongEpiMonoFactorisation_e]
  -- make separate lemma
  have : Abelian.factorThruImage f ≫ inv (Abelian.coimageImageComparison f) =
      Abelian.coimage.π f := by
    rw [← cancel_mono (Abelian.coimageImageComparison f)]
    simp [Abelian.coimageImageComparison]
  rw [reassoc_of% this]
  simp

end

namespace MonoOver

variable {X Y : C} (p : X ⟶ Y)

def existsAdjunction : MonoOver.exists p ⊣ MonoOver.pullback p :=
  Adjunction.mkOfHomEquiv
    { homEquiv A B :=
        { toFun f :=
            MonoOver.homMk (pullback.lift (factorThruImage (A.arrow ≫ p) ≫ f.left)
              A.arrow (by
                have := MonoOver.w f
                dsimp at this ⊢
                rw [Category.assoc, this, image.fac])) (by simp)
          invFun g := by
            have := MonoOver.w g
            dsimp at this
            refine MonoOver.homMk (image.desc _ (g.left ≫ pullback.fst _ _) ?_) ?_
            · rw [← cancel_mono B.arrow]
              dsimp
              rw [Category.assoc, Category.assoc, zero_comp, pullback.condition,
                reassoc_of% this, kernel.condition]
            · simp [← cancel_epi (factorThruImage _),
                pullback.condition, reassoc_of% this]
          left_inv _ := Subsingleton.elim _ _
          right_inv _ := Subsingleton.elim _ _ } }

@[reassoc (attr := simp)]
lemma factorThruImage_comp_existsAdjunction_counit_app_left (B : MonoOver Y) :
    factorThruImage (pullback.snd B.arrow p ≫ p) ≫
        ((existsAdjunction p).counit.app B).left = pullback.fst _ _ := by
  simp [existsAdjunction]

section

variable [Epi p]

instance (B : MonoOver Y) : Epi ((existsAdjunction p).counit.app B).left :=
  epi_of_epi_fac (factorThruImage_comp_existsAdjunction_counit_app_left p B)

instance (B : MonoOver Y) : IsIso ((existsAdjunction p).counit.app B) := by
  rw [isIso_iff_isIso_left]
  apply isIso_of_mono_of_epi

instance : IsIso (existsAdjunction p).counit :=
  NatIso.isIso_of_isIso_app _

end

end MonoOver

namespace Subobject

variable {X Y : C} (p : X ⟶ Y) [Epi p]

lemma exists_obj_pullback_obj_of_epi (A : Subobject Y) :
    (Subobject.exists p).obj ((pullback p).obj A) = A := by
  obtain ⟨A, i, _, rfl⟩ := A.mk_surjective
  exact ((equivMonoOver _).inverse.mapIso
    ((asIso ((MonoOver.existsAdjunction p).counit.app (.mk' i))))).to_eq

lemma pullback_obj_injective {X Y : C} (p : X ⟶ Y) [Epi p] :
    Function.Injective (Subobject.pullback p).obj := by
  intro A B h
  rw [← exists_obj_pullback_obj_of_epi p A, h, exists_obj_pullback_obj_of_epi]

end Subobject

end CategoryTheory
