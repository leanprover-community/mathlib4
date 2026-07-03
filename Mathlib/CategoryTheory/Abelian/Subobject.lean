/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
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

section

variable {X Y : C} (f : X ⟶ Y)

@[simp]
noncomputable
def Subobject.image {X Y : C} (f : X ⟶ Y) : Subobject X ⥤ Subobject Y where
  obj X' := imageSubobject (X'.arrow ≫ f)
  map {X' X''} h := by
    apply homOfLE
    exact (Eq.le (by simp)).trans (imageSubobject_comp_le (X'.ofLE X'' h.le) (X''.arrow ≫ f))

lemma Subobject.image_mono {X Y : C} (f : X ⟶ Y) [Mono f] {X' : Subobject X} :
    (image f).obj X' = Subobject.mk (X'.arrow ≫ f) := by
  simp [imageSubobject_mono]

/-
lemma Limits.imageSubobject_eq_of_arrowIso {X Y A : C} {f : X ⟶ Y} {g : A ⟶ Y}
    (e : Arrow.mk f ≅ Arrow.mk g) :imageSubobject f = imageSubobject g := by
  rw [Arrow.iso_w' e]
  have := Arrow.iso_w' e.symm
  simp at this
  erw [imageSubobject_iso_comp (Arrow.Hom.left e.inv) (f ≫ Arrow.Hom.right e.hom)]
  sorry
-/

lemma Subobject.image_mk_eq {X Y : C} (f : X ⟶ Y) {A : C} (g : A ⟶ X) [Mono g] :
    (image f).obj (Subobject.mk g) = imageSubobject (g ≫ f) := by
  simp only [← underlyingIso_arrow g =≫ f, Category.assoc, image, imageSubobject_iso_comp]

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

lemma Subobject.inverseImage_mk_eq {X Y : C} (f : X ⟶ Y) {A : C} (g : A ⟶ Y) [Mono g] :
    (inverseImage f).obj (Subobject.mk g) = kernelSubobject (f ≫ cokernel.π g) :=
  mk_eq_mk_of_comm _ _
    (kernel.mapIso _ _ (Iso.refl _)
      (cokernel.mapIso _ _ (underlyingIso _) (Iso.refl _) (by simp)) (by simp))
    (by simp)

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
  · rw [image_mono f, inverseImage_mk_eq]
    have := kernel.condition (f ≫ cokernel.π (X'.arrow ≫ f))
    rw [← Category.assoc] at this
    refine mk_le_of_comm (kernel.lift _ _ this ≫ (isoKernelCokernel (X'.arrow ≫ f)).inv) ?_
    rw [← cancel_mono f]
    simp
  · exact inverseImage_image_le f X'

@[simp]
lemma Subobject.epi_image_inverseImage {X Y : C} (f : X ⟶ Y) (Y' : Subobject Y) [Epi f] :
    (image f).obj ((inverseImage f).obj Y') = Y' := by
  apply le_antisymm (image_inverseImage_le f Y')
  dsimp only [inverseImage, kernelSubobject]
  rw [Subobject.image_mk_eq]
  let k : kernel (f ≫ cokernel.π Y'.arrow) ⟶ X := kernel.ι (f ≫ cokernel.π Y'.arrow)

  let v : kernel (f ≫ cokernel.π Y'.arrow) ⟶ Y' :=
    (kernel.lift (cokernel.π Y'.arrow) (k ≫ f) (by simp [k]) ≫ (isoKernelCokernel Y'.arrow).inv)

  have : IsLimit (PullbackCone.mk k v (show k ≫ f = v ≫ Y'.arrow by simp [k, v])) := by
    refine Limits.PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_
    · intro s
      exact kernel.lift (f ≫ cokernel.π Y'.arrow) s.fst
        (by simpa using s.condition =≫ cokernel.π Y'.arrow)
    · cat_disch
    · intro s
      simp [v, k, ← cancel_mono Y'.arrow, s.condition]
    · cat_disch

  have : Epi v := epi_snd_of_isLimit _ _ this

  have : Epi
      (kernel.lift (cokernel.π Y'.arrow) (kernel.ι (f ≫ cokernel.π Y'.arrow) ≫ f) (by simp)) := by
    dsimp [v] at this
    cat_disch

  have := strongEpi_of_epi
    (kernel.lift (cokernel.π Y'.arrow) (kernel.ι (f ≫ cokernel.π Y'.arrow) ≫ f) _)

  rw [← kernel.lift_ι (cokernel.π Y'.arrow) (kernel.ι (f ≫ cokernel.π Y'.arrow) ≫ f) (by simp),
    imageSubobject_epi_comp, imageSubobject_mono]
  exact le_kernelSubobject (cokernel.π Y'.arrow) Y' (cokernel.condition Y'.arrow)

end

end CategoryTheory.Abelian
