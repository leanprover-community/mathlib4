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

section

variable {X Y : C} (f : X ⟶ Y)

/-- A morphism `f : X ⟶ Y` induces a functor `Subobject X ⥤ Subobject Y`
  by `X' ↦ image (X' ⟶ X ⟶ Y)`. -/
@[simp]
noncomputable
def image : Subobject X ⥤ Subobject Y where
  obj X' := imageSubobject (X'.arrow ≫ f)
  map {X' X''} h := by
    apply homOfLE
    exact (Eq.le (by simp)).trans (imageSubobject_comp_le (X'.ofLE X'' h.le) (X''.arrow ≫ f))

lemma image_mono [Mono f] {X' : Subobject X} :
    (image f).obj X' = Subobject.mk (X'.arrow ≫ f) := by
  simp [imageSubobject_mono]

lemma image_mk_eq {A : C} (g : A ⟶ X) [Mono g] :
    (image f).obj (Subobject.mk g) = imageSubobject (g ≫ f) := by
  simp only [← underlyingIso_arrow g =≫ f, Category.assoc, image, imageSubobject_iso_comp]

lemma image_le {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : (image f).obj X' ≤ Y' :=
  imageSubobject_le (X'.arrow ≫ f) u h

/-- For `f : X ⟶ Y`, the canonical map from `X' : Subobject X` to `f(X') : Subobject Y`. -/
@[simp]
noncomputable
abbrev toImage {X Y : C} (X' : Subobject X) (f : X ⟶ Y) :
    (X' : C) ⟶ (image f).obj X' :=
  factorThruImageSubobject (X'.arrow ≫ f)

/-- A morphism `f : X ⟶ Y` induces a functor `Subobject Y ⥤ Subobject X`
  by `Y' ↦ kernel (X ⟶ Y ⟶ cokernel Y')`. -/
@[simp]
noncomputable
def inverseImage : Subobject Y ⥤ Subobject X where
  obj Y' := kernelSubobject (f ≫ cokernel.π Y'.arrow)
  map h :=
    homOfLE <| mk_le_mk_of_comm
      (kernel.map _ _ (𝟙 _) (cokernel.map _ _ (underlying.map h) (𝟙 _) (by simp)) (by simp))
      (by simp)

lemma inverseImage_mk_eq {A : C} (g : A ⟶ Y) [Mono g] :
    (inverseImage f).obj (Subobject.mk g) = kernelSubobject (f ≫ cokernel.π g) :=
  mk_eq_mk_of_comm _ _
    (kernel.mapIso _ _ (Iso.refl _)
      (cokernel.mapIso _ _ (underlyingIso _) (Iso.refl _) (by simp)) (by simp))
    (by simp)

/-- For `f : X ⟶ Y`, the canonical map from `f⁻¹(Y') : Subobject X` to `Y' : Subobject X`. -/
@[simp]
abbrev fromInverseImage {X Y : C} (Y' : Subobject Y) (f : X ⟶ Y) :
    (((inverseImage f).obj Y') : C) ⟶ Y' := (kernelSubobjectIso _).hom ≫
  kernel.lift (cokernel.π Y'.arrow) (kernel.ι (f ≫ cokernel.π Y'.arrow) ≫ f) (by simp) ≫
  (isoKernelCokernel _).inv

lemma le_inverseImage {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : X' ≤ (inverseImage f).obj Y' := by
  refine le_kernelSubobject (f ≫ cokernel.π Y'.arrow) X' ?_
  rw [← Category.assoc]
  simp [← h]

lemma inverseImage_image_le (X' : Subobject X) :
    X' ≤ (inverseImage f).obj ((image f).obj X') :=
  le_inverseImage _ (toImage _ _) (by simp)

lemma image_inverseImage_le (Y' : Subobject Y) :
    (image f).obj ((inverseImage f).obj Y') ≤ Y' :=
  image_le _ (fromInverseImage _ _) (by simp)

/-- If `f : X ⟶ Y` is a monomorphism in an abelian category, then `f⁻¹(f(X')) = X'`. -/
theorem mono_inverseImage_image (X' : Subobject X) [Mono f] :
    (inverseImage f).obj ((image f).obj X') = X' := by
  apply le_antisymm
  · rw [image_mono f, inverseImage_mk_eq]
    have := kernel.condition (f ≫ cokernel.π (X'.arrow ≫ f))
    rw [← Category.assoc] at this
    refine mk_le_of_comm (kernel.lift _ _ this ≫ (isoKernelCokernel (X'.arrow ≫ f)).inv) ?_
    rw [← cancel_mono f]
    simp
  · exact inverseImage_image_le f X'

set_option linter.style.emptyLine false in
/-- If `f : X ⟶ Y` is an epimorphism in an abelian category, then `f(f⁻¹(Y')) = Y'`. -/
theorem epi_image_inverseImage (Y' : Subobject Y) [Epi f] :
    (image f).obj ((inverseImage f).obj Y') = Y' := by
  apply le_antisymm (image_inverseImage_le f Y')
  dsimp only [inverseImage, kernelSubobject]
  let k : kernel (f ≫ cokernel.π Y'.arrow) ⟶ X := kernel.ι (f ≫ cokernel.π Y'.arrow)
  change Y' ≤ (image f).obj (Subobject.mk k)
  let v : kernel (f ≫ cokernel.π Y'.arrow) ⟶ Y' :=
    (kernel.lift (cokernel.π Y'.arrow) (k ≫ f) (by simp [k]) ≫ (isoKernelCokernel Y'.arrow).inv)
  /- First, we show the following square is a pullback:
     `ker (f ≫ coker.π Y')` -`v`-> `Y'`
              |                      |
             `k`                     |
              |                      |
              V                      v
             `X` -------`f`-------> `Y` -/
  have h : IsLimit (PullbackCone.mk k v (show k ≫ f = v ≫ Y'.arrow by simp [k, v])) := by
    refine PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_
    · intro s
      exact kernel.lift (f ≫ cokernel.π Y'.arrow) s.fst
        (by simpa using s.condition =≫ cokernel.π Y'.arrow)
    · cat_disch
    · intro s
      simp [v, k, ← cancel_mono Y'.arrow, s.condition]
    · cat_disch
  /- Because `C` is abelian and `f` is an epimorphism, the pullback above implies `v` is an epi. -/
  have : Epi v := epi_snd_of_isLimit _ _ h
  let : StrongEpi (kernel.lift (cokernel.π Y'.arrow) (k ≫ f) (by simp [k])) := by
    dsimp [v] at this
    rw [epi_comp_iff_of_isIso] at this
    exact strongEpi_of_epi (kernel.lift (cokernel.π Y'.arrow) (k ≫ f) _)
  /- Now `f(k) = image(k ≫ f)` because `k` is a mono.
              `= image(v ≫ kernel.ι)` by the kernel property.
              `= image(kernel.ι)` because `v` is an epi.
              `= kernel(cokernel.π Y')`
    From here it is straightforward that `Y' ≤ kernel(cokernel.π Y')`. -/
  rw [image_mk_eq, ← kernel.lift_ι (cokernel.π Y'.arrow) (k ≫ f) (by simp [k]),
    imageSubobject_epi_comp, imageSubobject_mono]
  exact le_kernelSubobject (cokernel.π Y'.arrow) Y' (cokernel.condition Y'.arrow)

set_option linter.style.emptyLine false in
open Subobject in
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
    apply le_antisymm
    · refine mk_le_of_comm ?_ ?_
      · dsimp
        refine kernel.lift _ (kernel.ι _) ?_ ≫ (isoKernelCokernel q.arrow).inv
        rw [← cokernel.π_desc Y.arrow (cokernel.π q.arrow) ((le_iff_comp_cokernel_zero Y q).mp hq),
          ← cokernel.π_desc (imageSubobject (q.arrow ≫ cokernel.π Y.arrow)).arrow
          (cokernel.desc Y.arrow (cokernel.π q.arrow) ((le_iff_comp_cokernel_zero Y q).mp hq))
          (imageSubobject_arrow_comp_eq_zero (by simp))]
        slice_lhs 2 4 => rw [← Category.assoc]
        simp only [kernel.condition_assoc, zero_comp]
      · simp
    · exact inverseImage_image_le _ _
  map_rel_iff' {a b} := by
    dsimp
    constructor
    · intro h
      have eq : kernel.ι (cokernel.π Y.arrow ≫ cokernel.π a.arrow) ≫
          cokernel.π Y.arrow ≫ cokernel.π b.arrow = 0 := by
        rw [← Preadditive.IsIso.comp_left_eq_zero (kernelSubobjectIso _).hom _, ← Category.assoc,
          kernelSubobject_arrow]
        simp only [← ofLE_arrow h, ← kernelSubobject_arrow, Category.assoc, kernel.condition,
          comp_zero]
      have := (cokernel.π_desc
            (kernel.ι (cokernel.π Y.arrow ≫ cokernel.π a.arrow))
            (cokernel.π Y.arrow ≫ cokernel.π b.arrow) eq)
      simp only [← comp_isoCokernelKernel_hom (cokernel.π Y.arrow ≫ cokernel.π a.arrow),
        Category.assoc, cancel_epi] at this
      rw [le_iff_comp_cokernel_zero, ← this]
      simp
    · intro h
      exact mk_le_mk_of_comm
        (kernel.map _ _ (𝟙 _) (cokernel.map _ _ (ofLE a b h) (𝟙 _) (by simp)) (by simp)) (by simp)

end

end CategoryTheory.Abelian.Subobject
