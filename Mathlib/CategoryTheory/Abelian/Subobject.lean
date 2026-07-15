/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Subobjects in abelian categories

This file contains numerous results about subobjects which are unique to abelian categories.

## Main results

* subobjects and quotient objects of an object `X` are order-isomorphic via taking kernels and
  cokernels
* a correspondence theorem: Given a subobject `Y` of `X`, `Abelian.Subobject.cokernelOrderIso` is
  an order-isomorphism between subobjects of `cokernel (Y ↪ X)` and subobjects of `X`
  containing `Y`.

## References

* [N. Popescu, *Abelian Categories with Applications to Rings and Modules*][popescu1973]

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

namespace Subobject

section SupBiproductFactorization

/-- If `C` is abelian and `f g : Subobject A`, then `f ⊞ g ⟶ A` factors as
  `f ⊞ g ⟶ f ⊔ g ⟶ A` -/
@[simps]
noncomputable
def supMonoFactorisation {A : C} (f g : Subobject A) : MonoFactorisation
    (biprod.desc f.arrow g.arrow) where
  I := underlying.obj (f ⊔ g)
  m := (f ⊔ g).arrow
  m_mono := inferInstance
  e := biprod.desc (ofLE f (f ⊔ g) le_sup_left) (ofLE g (f ⊔ g) le_sup_right)
  fac := by simp only [biprod.desc_eq, Preadditive.add_comp, Category.assoc, ofLE_arrow]

/-- If `C` is abelian, then `f ⊔ g` is an image of `f ⊞ g ⟶ A`. -/
@[simps]
noncomputable
def supIsImage {A : C} (f g : Subobject A) :
    IsImage (supMonoFactorisation f g) where
  lift F := by
    refine (f ⊔ g).ofLEMk F.m (sup_le ?_ ?_)
    · refine le_mk_of_comm (biprod.inl ≫ F.e) ?_
      · simp only [Category.assoc, MonoFactorisation.fac, biprod.inl_desc]
    · refine le_mk_of_comm (biprod.inr ≫ F.e) ?_
      · simp only [Category.assoc, MonoFactorisation.fac, biprod.inr_desc]
  lift_fac := by simp [supMonoFactorisation]

/-- If `C` is abelian, then `f ⊔ g ≅ image (f ⊞ g ⟶ A)`. -/
@[simps!]
noncomputable
def supIsoImage {A : C} (f g : Subobject A) : underlying.obj (f ⊔ g) ≅
    Limits.image (biprod.desc f.arrow g.arrow) :=
  IsImage.isoExt (supIsImage ..) <| Image.isImage _

lemma sup_eq_imageSubobject {A : C} (X Y : Subobject A) :
    X ⊔ Y = imageSubobject (biprod.desc X.arrow Y.arrow) := by
  refine eq_mk_of_comm (Limits.image.ι (biprod.desc X.arrow Y.arrow)) ?_ ?_
  · exact (supIsoImage X Y)
  · simp only [supIsoImage_hom]
    apply ofLEMk_comp

end SupBiproductFactorization

lemma le_iff_comp_cokernel_zero {X : C} (f g : Subobject X) :
    f ≤ g ↔ f.arrow ≫ cokernel.π (g.arrow) = 0 := by
  constructor
  · intro h
    rw [← ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
  · intro h
    exact le_of_comm
      (kernel.lift (cokernel.π g.arrow) f.arrow h ≫ (isoKernelCokernel g.arrow).inv) (by simp)

lemma imageSubobject_eq_kernelSubobject {X Y : C} (f : X ⟶ Y) :
    imageSubobject f = kernelSubobject (cokernel.π f) :=
  mk_eq_mk_of_comm (Limits.image.ι f) (kernel.ι (cokernel.π f)) (imageIsoImage f).symm
    (by simp only [Iso.symm_hom, imageIsoImage_inv, kernel.lift_ι])

section

variable {X Y : C} (f : X ⟶ Y)

/-- A morphism `f : X ⟶ Y` induces a functor `Subobject X ⥤ Subobject Y`
  by `X' ↦ kernel (cokernel.π (X'.arrow ≫ f))`. In an abelian category, this is the same
  as `image (X'.arrow ≫ f)`. -/
@[simp]
noncomputable
def image : Subobject X ⥤ Subobject Y where
  obj X' := kernelSubobject (cokernel.π (X'.arrow ≫ f))
  map {X' X''} h := homOfLE <| mk_le_mk_of_comm
    (kernel.map _ _ (𝟙 _) (cokernel.map _ _ (X'.ofLE X'' h.le) (𝟙 _) (by simp)) (by simp))
    (by simp)

lemma image_eq_imageSubobject {X' : Subobject X} :
    (image f).obj X' = imageSubobject (X'.arrow ≫ f) := by
  simp only [← underlyingIso_arrow X'.arrow =≫ f, Category.assoc, image, imageSubobject_iso_comp]
  rw [imageSubobject_eq_kernelSubobject]
  exact mk_eq_mk_of_comm _ _
    (kernel.mapIso _ _ (Iso.refl _)
      (cokernel.mapIso _ _ (underlyingIso _).symm (Iso.refl _) (by simp)) (by simp)) (by simp)

lemma image_mk_eq_imageSubobject {A : C} (g : A ⟶ X) [Mono g] :
    (image f).obj (Subobject.mk g) = imageSubobject (g ≫ f) := by
  simp only [← underlyingIso_arrow g =≫ f, Category.assoc, image, imageSubobject_iso_comp]
  exact mk_eq_mk_of_comm _ _ (imageIsoImage _) (imageIsoImage_hom_comp_image_ι _)

lemma image_mono [Mono f] {X' : Subobject X} :
    (image f).obj X' = Subobject.mk (X'.arrow ≫ f) :=
  mk_eq_mk_of_comm _ _ (isoKernelCokernel _).symm (by simp)

lemma image_le {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : (image f).obj X' ≤ Y' := by
  rw [image_eq_imageSubobject]
  exact imageSubobject_le (X'.arrow ≫ f) u h

/-- For `f : X ⟶ Y`, the canonical map from `X' : Subobject X` to `f(X') : Subobject Y`. -/
@[simp]
noncomputable
abbrev toImage {X Y : C} (X' : Subobject X) (f : X ⟶ Y) :
    (X' : C) ⟶ (image f).obj X' :=
  factorThruKernelSubobject (cokernel.π (X'.arrow ≫ f)) (X'.arrow ≫ f) (cokernel.condition _)

/-- A morphism `f : X ⟶ Y` induces a functor `Subobject Y ⥤ Subobject X`
  by `Y' ↦ kernel (f ≫ cokernel.π Y'.arrow)`. -/
@[simp]
noncomputable
def inverseImage : Subobject Y ⥤ Subobject X where
  obj Y' := kernelSubobject (f ≫ cokernel.π Y'.arrow)
  map h := homOfLE <| mk_le_mk_of_comm
    (kernel.map _ _ (𝟙 _) (cokernel.map _ _ (underlying.map h) (𝟙 _) (by simp)) (by simp))
    (by simp)

lemma inverseImage_mk_eq_kernelSubobject {A : C} (g : A ⟶ Y) [Mono g] :
    (inverseImage f).obj (Subobject.mk g) = kernelSubobject (f ≫ cokernel.π g) :=
  mk_eq_mk_of_comm _ _
    (kernel.mapIso _ _ (Iso.refl _)
      (cokernel.mapIso _ _ (underlyingIso _) (Iso.refl _) (by simp)) (by simp))
    (by simp)

lemma le_inverseImage {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : X' ≤ (inverseImage f).obj Y' := by
  refine le_kernelSubobject (f ≫ cokernel.π Y'.arrow) X' ?_
  rw [← Category.assoc]
  simp [← h]

/-- For `f : X ⟶ Y`, the canonical map from `f⁻¹(Y') : Subobject X` to `Y' : Subobject X`. -/
@[simp]
abbrev fromInverseImage {X Y : C} (Y' : Subobject Y) (f : X ⟶ Y) :
    (((inverseImage f).obj Y') : C) ⟶ Y' := (kernelSubobjectIso _).hom ≫
  kernel.lift (cokernel.π Y'.arrow) (kernel.ι (f ≫ cokernel.π Y'.arrow) ≫ f) (by simp) ≫
  (isoKernelCokernel _).inv

lemma inverseImage_image_le (X' : Subobject X) :
    X' ≤ (inverseImage f).obj ((image f).obj X') :=
  le_inverseImage _ (toImage _ _) (by simp)

lemma image_inverseImage_le (Y' : Subobject Y) :
    (image f).obj ((inverseImage f).obj Y') ≤ Y' :=
  image_le _ (fromInverseImage _ _) (by simp)

lemma image_le_image_iff_of_mono (X₁ X₂ : Subobject X) [Mono f] :
    (image f).obj X₁ ≤ (image f).obj X₂ ↔ X₁ ≤ X₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ (image f).monotone h⟩
  simp only [image_mono f] at h
  exact le_of_comm (ofMkLEMk (X₁.arrow ≫ f) (X₂.arrow ≫ f) h)
    (by rw [← cancel_mono f, Category.assoc, ofMkLEMk_comp])

/-- If `f : X ⟶ Y` is a monomorphism in an abelian category, then `f⁻¹(f(X')) = X'`. -/
theorem mono_inverseImage_image (X' : Subobject X) [Mono f] :
    (inverseImage f).obj ((image f).obj X') = X' :=
  le_antisymm ((image_le_image_iff_of_mono f _ _).mp (image_inverseImage_le f _))
    (inverseImage_image_le f X')

lemma inverseImage_le_inverseImage_iff_of_epi (Y₁ Y₂ : Subobject Y) [Epi f] :
    (inverseImage f).obj Y₁ ≤ (inverseImage f).obj Y₂ ↔ Y₁ ≤ Y₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ (inverseImage f).monotone h⟩
  dsimp at h
  let d := epiDesc (f ≫ cokernel.π Y₁.arrow) (f ≫ cokernel.π Y₂.arrow) (by
    rw [← kernelSubobject_arrow' (f ≫ cokernel.π Y₁.arrow), ← ofLE_arrow h]
    simp only [Category.assoc, kernelSubobject_arrow_comp, comp_zero])
  have hd : cokernel.π Y₁.arrow ≫ d = cokernel.π Y₂.arrow := by
    rw [← cancel_epi f, ← Category.assoc]
    exact comp_epiDesc _ _ _
  simp [le_iff_comp_cokernel_zero, ← hd]

/-- If `f : X ⟶ Y` is an epimorphism in an abelian category, then `f(f⁻¹(Y')) = Y'`. -/
theorem epi_image_inverseImage (Y' : Subobject Y) [Epi f] :
    (image f).obj ((inverseImage f).obj Y') = Y' :=
  le_antisymm (image_inverseImage_le f Y')
    ((inverseImage_le_inverseImage_iff_of_epi f _ _).mp (inverseImage_image_le f _))

/-- Given a subobject `Y` of `X`, there is an order-isomorphism between subobjects
of `X/Y := cokernel (Y ↪ X)` and subobjects of `X` containing `Y`. -/
noncomputable
def cokernelOrderIso (Y : Subobject X) :
    Subobject (cokernel Y.arrow) ≃o Set.Ici Y where
  toFun p := ⟨(inverseImage (cokernel.π Y.arrow)).obj p, le_kernelSubobject _ _ (by simp)⟩
  invFun q := (image (cokernel.π Y.arrow)).obj q
  left_inv p := epi_image_inverseImage (cokernel.π Y.arrow) p
  right_inv := by
    rintro ⟨q, hq : Y ≤ q⟩
    let d := cokernel.desc Y.arrow (cokernel.π q.arrow) ((le_iff_comp_cokernel_zero Y q).mp hq)
    have : Epi d := epi_of_epi_fac (cokernel.π_desc _ _ _)
    have hq' : (inverseImage (cokernel.π Y.arrow)).obj (kernelSubobject d) = q := by
      rw [inverseImage_mk_eq_kernelSubobject, ← comp_isoCokernelKernel_hom d]
      simp only [← Category.assoc, d, cokernel.π_desc, kernelSubobject_comp_mono]
      rw [← imageSubobject_eq_kernelSubobject, imageSubobject_mono]
      exact mk_arrow q
    simp only [Subtype.mk.injEq]
    change (inverseImage (cokernel.π Y.arrow)).obj ((image (cokernel.π Y.arrow)).obj q) = q
    rw [← hq', epi_image_inverseImage]
  map_rel_iff' := inverseImage_le_inverseImage_iff_of_epi _ _ _

end

end CategoryTheory.Abelian.Subobject
