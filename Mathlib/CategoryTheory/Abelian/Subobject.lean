/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Equivalence between subobjects and quotients in an abelian category

-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits Opposite Subobject

universe w v u

noncomputable section

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.defeqAttrib.useBackward true in
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

section Sup

@[simps]
noncomputable
def Subobject.sup_MonoFactorisation {A : C} (f g : Subobject A) : MonoFactorisation
    (biprod.desc f.arrow g.arrow) where
  I := underlying.obj (f ⊔ g)
  m := (f ⊔ g).arrow
  m_mono := inferInstance
  e := biprod.desc (ofLE f (f ⊔ g) le_sup_left) (ofLE g (f ⊔ g) le_sup_right)
  fac := by simp only [biprod.desc_eq, Preadditive.add_comp, Category.assoc, ofLE_arrow]

@[simps]
noncomputable
def Subobject.sup_isImage {A : C} (f g : Subobject A) :
    IsImage (sup_MonoFactorisation f g) where
  lift F := by
    refine (f ⊔ g).ofLEMk F.m (sup_le ?_ ?_)
    · refine le_mk_of_comm (biprod.inl ≫ F.e) ?_
      · simp only [Category.assoc, MonoFactorisation.fac, biprod.inl_desc]
    · refine le_mk_of_comm (biprod.inr ≫ F.e) ?_
      · simp only [Category.assoc, MonoFactorisation.fac, biprod.inr_desc]
  lift_fac := by simp [sup_MonoFactorisation]

@[simps!]
noncomputable
def Subobject.sup_isoImage {A : C} (f g : Subobject A) : underlying.obj (f ⊔ g) ≅
    Limits.image (biprod.desc f.arrow g.arrow) :=
  IsImage.isoExt (sup_isImage ..) <| Image.isImage _

end Sup

noncomputable section Image

variable {X Y : C} (f : X ⟶ Y)

/-- The image of a morphism `f g : X ⟶ Y` as a `Subobject Y`. -/
abbrev abImageSubobject : Subobject Y :=
  Subobject.mk (Abelian.image.ι f)

/-- The underlying object of `abImageSubobject f` is (up to isomorphism!)
the same as the chosen object `Abelian.image f`. -/
def abImageSubobjectIso : (abImageSubobject f : C) ≅ Abelian.image f :=
  Subobject.underlyingIso (Abelian.image.ι f)

@[reassoc (attr := simp)]
theorem abImageSubobject_arrow :
    (abImageSubobjectIso f).hom ≫ Abelian.image.ι f =
      (abImageSubobject f).arrow := by simp [abImageSubobjectIso]

@[reassoc (attr := simp)]
theorem abImageSubobject_arrow' :
    (abImageSubobjectIso f).inv ≫ (abImageSubobject f).arrow = Abelian.image.ι f := by
  simp [abImageSubobjectIso]

/-- A factorisation of `f : X ⟶ Y` through `abImageSubobject f`. -/
def factorThruAbImageSubobject : X ⟶ abImageSubobject f :=
  Abelian.factorThruImage f ≫ (abImageSubobjectIso f).inv

instance : Epi (factorThruAbImageSubobject f) := by
  dsimp [factorThruAbImageSubobject]
  apply epi_comp

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem abImageSubobject_arrow_comp :
    factorThruAbImageSubobject f ≫ (abImageSubobject f).arrow = f := by
  simp [factorThruAbImageSubobject]

theorem abImageSubobject_arrow_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0) :
    (abImageSubobject f).arrow ≫ g = 0 :=
  zero_of_epi_comp (factorThruAbImageSubobject f) <| by simp [h]

theorem abImageSubobject_factors_comp_self {W : C} (k : W ⟶ X) :
    (abImageSubobject f).Factors (k ≫ f) :=
  ⟨k ≫ Abelian.factorThruImage f, by simp⟩

@[simp]
theorem factorThruAbImageSubobject_comp_self {W : C} (k : W ⟶ X) (h) :
    (abImageSubobject f).factorThru (k ≫ f) h = k ≫ factorThruAbImageSubobject f := by
  ext
  simp

@[simp]
theorem factorThruAbImageSubobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h) :
    (abImageSubobject f).factorThru (k ≫ k' ≫ f) h = k ≫ k' ≫ factorThruAbImageSubobject f := by
  ext
  simp

/-- The image of `h ≫ f` is always a smaller subobject than the image of `f`. -/
theorem abImageSubobject_comp_le {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) :
    abImageSubobject (h ≫ f) ≤ abImageSubobject f := by
  refine Subobject.mk_le_mk_of_comm (kernel.lift _ (Abelian.image.ι (h ≫ f)) (by simp)) (by simp)

end Image

section

variable {X Y : C} (f : X ⟶ Y)

@[simp]
noncomputable
def Subobject.image {X Y : C} (f : X ⟶ Y) : Subobject X ⥤ Subobject Y where
  obj X' := abImageSubobject (X'.arrow ≫ f)
  map := by
    intro X' X'' h
    refine homOfLE (le_of_comm (kernelSubobjectMap (Arrow.homMk' ?_ ?_ ?_)) ?_)
    · exact 𝟙 _
    · apply cokernel.desc _ (cokernel.π (X''.arrow ≫ f))
      · simp
        sorry
    · simp
    · simp only [kernelSubobjectMap_arrow, Arrow.homMk'_left]
      exact Category.comp_id (kernelSubobject (cokernel.π (X'.arrow ≫ f))).arrow

@[simp]
noncomputable
def Subobject.image_map {X Y : C} (f : X ⟶ Y) (X' : Subobject X) :
    underlying.obj X' ⟶ underlying.obj (abImageSubobject (X'.arrow ≫ f)) :=
  factorThruAbImageSubobject (X'.arrow ≫ f)
  --Abelian.coimage.π (X'.arrow ≫ f) ≫ Abelian.coimageImageComparison (X'.arrow ≫ f)

@[simp]
noncomputable
def Subobject.inverseImage {X Y : C} (f : X ⟶ Y) : Subobject Y ⥤ Subobject X where
  obj Y' := kernelSubobject (f ≫ cokernel.π Y'.arrow)
  map := sorry
  map_id := sorry
  map_comp := sorry

@[simp]
noncomputable
def Subobject.inverseImage' {X Y : C} (f : X ⟶ Y) : Subobject Y ⥤ Subobject X := pullback f

def Subobject.inverseImage_inc (Y' : Subobject Y) :
    kernel f ⟶ kernel (f ≫ cokernel.π Y'.arrow) := by
  sorry

lemma Subobject.inverseImage_comp {X Y : C} (f : X ⟶ Y) (Y' : Subobject Y) :
    sorry ≫ Y'.arrow = ((inverseImage f).obj Y').arrow ≫ f := by
  simp
  have : kernel (f ≫ cokernel.π Y'.arrow) ⟶ Y' := by
    sorry
  sorry

end

end CategoryTheory.Abelian
