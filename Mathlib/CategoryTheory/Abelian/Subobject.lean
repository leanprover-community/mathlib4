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

lemma Subobject.sup_eq_imageSubobject {A : C} (X Y : Subobject A) :
    X ⊔ Y = imageSubobject (biprod.desc X.arrow Y.arrow) := by
  refine eq_mk_of_comm (Limits.image.ι (biprod.desc X.arrow Y.arrow)) ?_ ?_
  · exact (sup_isoImage X Y)
  · simp only [sup_isoImage_hom]
    apply ofLEMk_comp

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
  obj X' := imageSubobject (X'.arrow ≫ f)
  map {X' X''} h := by
    apply homOfLE
    exact (Eq.le (by simp)).trans (imageSubobject_comp_le (X'.ofLE X'' h.le) (X''.arrow ≫ f))

lemma Subobject.image_le {X Y : C} (f : X ⟶ Y) {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : (image f).obj X' ≤ Y' :=
  imageSubobject_le (X'.arrow ≫ f) u h

@[simp]
noncomputable
def Subobject.image_map {X Y : C} (f : X ⟶ Y) (X' : Subobject X) :
    (X' : C) ⟶ (image f).obj X' :=
  factorThruImageSubobject (X'.arrow ≫ f)

@[simp]
noncomputable
def Subobject.inverseImage {X Y : C} (f : X ⟶ Y) : Subobject Y ⥤ Subobject X where
  obj Y' := kernelSubobject (f ≫ cokernel.π Y'.arrow)
  map {Y' Y''} h := by
    apply homOfLE
    refine mk_le_mk_of_comm ?_ ?_
    · exact kernel.map (f ≫ cokernel.π Y'.arrow) (f ≫ cokernel.π Y''.arrow) (𝟙 _)
        (cokernel.map Y'.arrow Y''.arrow (underlying.map h) (𝟙 _) (by simp)) (by simp)
    · simp

def Subobject.isoKernelCokernel {X Y : C} {A : Subobject X} (f : (A : C) ⟶ Y) [Mono f] :
    (A : C) ≅ kernel (cokernel.π f) := by
  have := ((monoIsKernelOfCokernel _ (cokernelIsCokernel f)).conePointUniqueUpToIso
    (kernelIsKernel (cokernel.π f)))
  exact this

@[simp]
lemma Subobject.isoKernelCokernel_hom_arrow {X Y : C} {A : Subobject X} (f : (A : C) ⟶ Y) [Mono f] :
    (isoKernelCokernel f).hom ≫ kernel.ι (cokernel.π f) = f :=
  (IsLimit.conePointUniqueUpToIso_hom_comp _ _) WalkingParallelPair.zero

@[simp]
lemma Subobject.isoKernelCokernel_inv_arrow {A Y : C} {X : Subobject A} (f : (X : C) ⟶ Y) [Mono f] :
    (isoKernelCokernel f).inv ≫ f = kernel.ι (cokernel.π f) :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _) WalkingParallelPair.zero

/-
@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_inv_desc]
theorem lift_comp_conePointUniqueUpToIso_hom {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t) :
    P.lift r ≫ (conePointUniqueUpToIso P Q).hom = Q.lift r :=
  Q.uniq _ _ (by simp)

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_hom_desc]
theorem lift_comp_conePointUniqueUpToIso_inv {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t) :
    Q.lift r ≫ (conePointUniqueUpToIso P Q).inv = P.lift r :=
  P.uniq _ _ (by simp)
-/


@[simp]
def Subobject.inverseImage_map {X Y : C} (f : X ⟶ Y) (Y' : Subobject Y) :
    (((inverseImage f).obj Y') : C) ⟶ Y' := (kernelSubobjectIso _).hom ≫
  kernel.lift (cokernel.π Y'.arrow) (kernel.ι (f ≫ cokernel.π Y'.arrow) ≫ f) (by simp) ≫
  (isoKernelCokernel _).inv

lemma Subobject.le_inverseImage {X Y : C} (f : X ⟶ Y) {X' : Subobject X} {Y' : Subobject Y}
    (u : (X' : C) ⟶ Y') (h : u ≫ Y'.arrow = X'.arrow ≫ f) : X' ≤ (inverseImage f).obj Y' := by
  refine le_kernelSubobject (f ≫ cokernel.π Y'.arrow) X' ?_
  rw [← Category.assoc]
  simp [← h]

lemma Subobject.inverseImage_image_le {X Y : C} (f : X ⟶ Y) (X' : Subobject X) :
    X' ≤ (inverseImage f).obj ((image f).obj X') :=
  le_inverseImage _ (factorThruImageSubobject _) (by simp)

lemma Subobject.image_inverseImage_le {X Y : C} (f : X ⟶ Y) (Y' : Subobject Y) :
    (image f).obj ((inverseImage f).obj Y') ≤ Y' :=
  image_le _ (inverseImage_map f Y') (by simp)

@[simp]
lemma Subobject.mono_inverseImage_image {X Y : C} (f : X ⟶ Y) (X' : Subobject X) [Mono f] :
    (inverseImage f).obj ((image f).obj X') = X' := by
  apply le_antisymm
  · refine mk_le_of_comm ?_ ?_
    · simp only [image, homOfLE_leOfHom]
      sorry
    · sorry
  · exact inverseImage_image_le f X'

@[simp]
lemma Subobject.epi_image_inverseImage {X Y : C} (f : X ⟶ Y) (Y' : Subobject Y) [Epi f] :
    (image f).obj ((inverseImage f).obj Y') = Y' := by
  apply le_antisymm
  · exact image_inverseImage_le f Y'
  · refine le_of_comm ?_ ?_
    · simp
      sorry
    · sorry

/-
lemma Subobject.inverseImage_comp {X Y : C} (f : X ⟶ Y) (Y' : Subobject Y) :
    (inverseImage_map f Y') ≫ Y'.arrow = ((inverseImage f).obj Y').arrow ≫ f := by
  simp
-/

end

end CategoryTheory.Abelian
