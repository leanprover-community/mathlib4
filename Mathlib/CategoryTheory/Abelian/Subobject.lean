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
* `inverseImage_directImage_eq_sup` and `directImage_inverseImage_eq_inf` describe the closure and
  interior operators induced by direct and inverse image
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

lemma sup_eq_imageSubobject {A : C} (X Y : Subobject A) :
    X ⊔ Y = imageSubobject (biprod.desc X.arrow Y.arrow) := by
  rw [CategoryTheory.Subobject.sup_eq_imageSubobject,
    ← imageSubobject_iso_comp (biprod.isoCoprod _ _).hom (coprod.desc X.arrow Y.arrow)]
  congr 1
  ext <;> simp only [biprod_isoCoprod_hom, ← Category.assoc, biprod.inl_desc,
    biprod.inr_desc, coprod.inl_desc, coprod.inr_desc]

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
  as `image (X'.arrow ≫ f)`: see `directImage_eq_imageSubobject`. -/
@[simp]
noncomputable
def directImage : Subobject X ⥤ Subobject Y where
  obj X' := kernelSubobject (cokernel.π (X'.arrow ≫ f))
  map {X' X''} h := homOfLE <| mk_le_mk_of_comm
    (kernel.map _ _ (𝟙 _) (cokernel.map _ _ (X'.ofLE X'' h.le) (𝟙 _) (by simp)) (by simp))
    (by simp)

lemma directImage_eq_imageSubobject {X' : Subobject X} :
    (directImage f).obj X' = imageSubobject (X'.arrow ≫ f) := by
  simp only [← underlyingIso_arrow X'.arrow =≫ f, Category.assoc, directImage,
    imageSubobject_iso_comp]
  rw [imageSubobject_eq_kernelSubobject]
  exact mk_eq_mk_of_comm _ _
    (kernel.mapIso _ _ (Iso.refl _)
      (cokernel.mapIso _ _ (underlyingIso _).symm (Iso.refl _) (by simp)) (by simp)) (by simp)

/-- The kernel-cokernel definition of direct image agrees with the generic direct image of
subobjects. -/
lemma directImage_eq_exists (X' : Subobject X) :
    (directImage f).obj X' = (Subobject.«exists» f).obj X' := by
  rw [directImage_eq_imageSubobject]
  apply Subobject.eq_of_comm
    ((imageSubobjectIso (X'.arrow ≫ f)).trans (Subobject.existsIsoImage f X').symm)
  have h : (Subobject.existsIsoImage f X').inv ≫
      ((Subobject.«exists» f).obj X').arrow = Limits.image.ι (X'.arrow ≫ f) := by
    rw [Iso.inv_comp_eq]
    exact (Over.w ((Subobject.existsCompRepresentativeIso f).app X').hom.hom).symm
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, h, imageSubobject_arrow]

lemma directImage_mk_eq_imageSubobject {A : C} (g : A ⟶ X) [Mono g] :
    (directImage f).obj (Subobject.mk g) = imageSubobject (g ≫ f) := by
  rw [directImage_eq_imageSubobject]
  simp only [← underlyingIso_arrow g =≫ f, Category.assoc, imageSubobject_iso_comp]

lemma directImage_mono [Mono f] {X' : Subobject X} :
    (directImage f).obj X' = Subobject.mk (X'.arrow ≫ f) := by
  rw [directImage_eq_imageSubobject, imageSubobject_mono]

lemma directImage_le {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : (directImage f).obj X' ≤ Y' := by
  rw [directImage_eq_imageSubobject]
  exact imageSubobject_le (X'.arrow ≫ f) u h

/-- For `f : X ⟶ Y`, the canonical map from `X' : Subobject X` to `f(X') : Subobject Y`. -/
@[simp]
noncomputable
abbrev toDirectImage {X Y : C} (X' : Subobject X) (f : X ⟶ Y) :
    (X' : C) ⟶ (directImage f).obj X' :=
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

/-- For `f : X ⟶ Y`, the canonical map from `f⁻¹(Y') : Subobject X` to `Y' : Subobject Y`. -/
@[simp]
abbrev fromInverseImage {X Y : C} (Y' : Subobject Y) (f : X ⟶ Y) :
    (((inverseImage f).obj Y') : C) ⟶ Y' := (kernelSubobjectIso _).hom ≫
  kernel.lift (cokernel.π Y'.arrow) (kernel.ι (f ≫ cokernel.π Y'.arrow) ≫ f) (by simp) ≫
  (isoKernelCokernel _).inv

theorem directImage_inverseImage_gc :
    GaloisConnection (directImage f).obj (inverseImage f).obj := fun X' Y' ↦
  ⟨fun h ↦ le_inverseImage f (toDirectImage X' f ≫ ofLE _ _ h) (by simp),
    fun h ↦ directImage_le f (ofLE _ _ h ≫ fromInverseImage Y' f) (by simp)⟩

/-- The kernel definition of inverse image agrees with the generic pullback of subobjects. -/
lemma inverseImage_eq_pullback (Y' : Subobject Y) :
    (inverseImage f).obj Y' = (Subobject.pullback f).obj Y' := by
  let gc : GaloisConnection (Subobject.«exists» f).obj (Subobject.pullback f).obj :=
    fun X' Y' ↦
      ⟨fun h ↦ ((Subobject.existsPullbackAdj f).homEquiv _ _ (homOfLE h)).le,
        fun h ↦ ((Subobject.existsPullbackAdj f).homEquiv _ _).symm (homOfLE h) |>.le⟩
  exact (directImage_inverseImage_gc f).u_unique gc (directImage_eq_exists f)

/-- Inverse image commutes with composition. -/
lemma inverseImage_comp {Z : C} (g : Y ⟶ Z) (Z' : Subobject Z) :
    (inverseImage (f ≫ g)).obj Z' =
      (inverseImage f).obj ((inverseImage g).obj Z') := by
  rw [inverseImage_eq_pullback, inverseImage_eq_pullback, inverseImage_eq_pullback,
    ← Subobject.pullback_comp]

/-- Direct image commutes with composition. -/
lemma directImage_comp {Z : C} (g : Y ⟶ Z) (X' : Subobject X) :
    (directImage (f ≫ g)).obj X' = (directImage g).obj ((directImage f).obj X') :=
  (directImage_inverseImage_gc (f ≫ g)).l_unique
    ((directImage_inverseImage_gc f).compose (directImage_inverseImage_gc g))
    (inverseImage_comp f g)

lemma inverseImage_directImage_le (X' : Subobject X) :
    X' ≤ (inverseImage f).obj ((directImage f).obj X') := (directImage_inverseImage_gc f).le_u_l X'

lemma directImage_inverseImage_le (Y' : Subobject Y) :
    (directImage f).obj ((inverseImage f).obj Y') ≤ Y' := (directImage_inverseImage_gc f).l_u_le Y'

lemma directImage_le_directImage_iff_of_mono (X₁ X₂ : Subobject X) [Mono f] :
    (directImage f).obj X₁ ≤ (directImage f).obj X₂ ↔ X₁ ≤ X₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ (directImage f).monotone h⟩
  simp only [directImage_mono f] at h
  exact le_of_comm (ofMkLEMk (X₁.arrow ≫ f) (X₂.arrow ≫ f) h)
    (by rw [← cancel_mono f, Category.assoc, ofMkLEMk_comp])

/-- If `f : X ⟶ Y` is a monomorphism in an abelian category, then `f⁻¹(f(X')) = X'`. -/
theorem mono_inverseImage_directImage (X' : Subobject X) [Mono f] :
    (inverseImage f).obj ((directImage f).obj X') = X' :=
  le_antisymm ((directImage_le_directImage_iff_of_mono f _ _).mp (directImage_inverseImage_le f _))
    (inverseImage_directImage_le f X')

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
theorem epi_directImage_inverseImage (Y' : Subobject Y) [Epi f] :
    (directImage f).obj ((inverseImage f).obj Y') = Y' :=
  le_antisymm (directImage_inverseImage_le f Y')
    ((inverseImage_le_inverseImage_iff_of_epi f _ _).mp (inverseImage_directImage_le f _))

theorem inverseImage_directImage_eq_self_of_epi [Epi f] (X' : Subobject X)
    (h : kernelSubobject f ≤ X') : (inverseImage f).obj ((directImage f).obj X') = X' := by
  let d := epiDesc f (cokernel.π X'.arrow) (by
    rw [← kernelSubobject_arrow' f, ← ofLE_arrow h]
    simp only [Category.assoc, cokernel.condition, comp_zero])
  have : Epi d := epi_of_epi_fac (comp_epiDesc f (cokernel.π X'.arrow) _)
  have hX' : (inverseImage f).obj (kernelSubobject d) = X' := by
    rw [inverseImage_mk_eq_kernelSubobject, ← comp_isoCokernelKernel_hom d]
    simp only [← Category.assoc, d, comp_epiDesc, kernelSubobject_comp_mono]
    rw [← imageSubobject_eq_kernelSubobject, imageSubobject_mono]
    exact mk_arrow X'
  rw [← hX', epi_directImage_inverseImage]

/-- For an epimorphism, taking direct image and then inverse image adds its kernel. -/
lemma inverseImage_directImage_eq_sup_of_epi [Epi f] (X' : Subobject X) :
    (inverseImage f).obj ((directImage f).obj X') = X' ⊔ kernelSubobject f := by
  apply le_antisymm
  · rw [← inverseImage_directImage_eq_self_of_epi f
      (X' ⊔ kernelSubobject f) le_sup_right]
    exact (inverseImage f).monotone ((directImage f).monotone le_sup_left)
  · apply sup_le (inverseImage_directImage_le f X')
    exact kernelSubobject_comp_le f _

/-- Taking direct image and then inverse image adds the kernel of the morphism. -/
lemma inverseImage_directImage_eq_sup (X' : Subobject X) :
    (inverseImage f).obj ((directImage f).obj X') = X' ⊔ kernelSubobject f := by
  rw [← imageSubobject_arrow_comp f, directImage_comp, inverseImage_comp,
    mono_inverseImage_directImage, inverseImage_directImage_eq_sup_of_epi,
    kernelSubobject_comp_mono]

/-- For a monomorphism, taking inverse image and then direct image intersects with its image. -/
lemma directImage_inverseImage_eq_inf_of_mono [Mono f] (Y' : Subobject Y) :
    (directImage f).obj ((inverseImage f).obj Y') = Y' ⊓ imageSubobject f := by
  rw [directImage_eq_exists, inverseImage_eq_pullback, Subobject.exists_iso_map]
  change (Subobject.map (MonoOver.mk f).arrow).obj
      ((Subobject.pullback (MonoOver.mk f).arrow).obj Y') = _
  rw [← Subobject.inf_eq_map_pullback' (MonoOver.mk f) Y']
  change Subobject.mk f ⊓ Y' = _
  rw [imageSubobject_mono, inf_comm]

/-- Taking inverse image and then direct image intersects with the image of the morphism. -/
lemma directImage_inverseImage_eq_inf (Y' : Subobject Y) :
    (directImage f).obj ((inverseImage f).obj Y') = Y' ⊓ imageSubobject f := by
  conv_lhs =>
    rw [← imageSubobject_arrow_comp f, directImage_comp, inverseImage_comp,
      epi_directImage_inverseImage, directImage_inverseImage_eq_inf_of_mono]
  rw [imageSubobject_mono, mk_arrow]

/-- Given a subobject `Y` of `X`, there is an order-isomorphism between subobjects
of `X/Y := cokernel (Y ↪ X)` and subobjects of `X` containing `Y`. -/
noncomputable
def cokernelOrderIso (Y : Subobject X) :
    Subobject (cokernel Y.arrow) ≃o Set.Ici Y where
  toFun p := ⟨(inverseImage (cokernel.π Y.arrow)).obj p, le_kernelSubobject _ _ (by simp)⟩
  invFun q := (directImage (cokernel.π Y.arrow)).obj q
  left_inv p := epi_directImage_inverseImage (cokernel.π Y.arrow) p
  right_inv := by
    rintro ⟨q, hq : Y ≤ q⟩
    ext1
    exact inverseImage_directImage_eq_self_of_epi _ _
      (by rwa [← imageSubobject_eq_kernelSubobject, imageSubobject_mono, mk_arrow])
  map_rel_iff' := inverseImage_le_inverseImage_iff_of_epi _ _ _

end

end CategoryTheory.Abelian.Subobject
