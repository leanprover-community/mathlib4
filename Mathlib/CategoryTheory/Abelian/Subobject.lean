/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Abelian.Regular
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Order.Atoms

/-!
# Subobjects in abelian categories

This file contains numerous results about subobjects which are unique to abelian categories.

## Main results

* subobjects and quotient objects of an object `X` are order-isomorphic via taking kernels and
  cokernels
* a correspondence theorem: Given a subobject `Y` of `X`, `Abelian.Subobject.cokernelOrderIso` is
  an order-isomorphism between subobjects of `cokernel (Y ↪ X)` and subobjects of `X`
  containing `Y`.
* the kernel-cokernel definitions of direct and inverse image agree with `Subobject.«exists»` and
  `Subobject.pullback`, respectively
* `directImage_inf_inverseImage` expresses Frobenius reciprocity for direct and inverse image

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

/-- Direct image satisfies Frobenius reciprocity with inverse image in an abelian category. -/
lemma directImage_inf_inverseImage (X' : Subobject X) (Y' : Subobject Y) :
    (directImage f).obj (X' ⊓ (inverseImage f).obj Y') = (directImage f).obj X' ⊓ Y' := by
  rw [directImage_eq_exists, inverseImage_eq_pullback, directImage_eq_exists]
  exact Regular.exists_inf_pullback_eq_exists_inf f X' Y'

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

section IsSimpleSubobject

/-- An object is simple when it has only two subobjects, `⊥` and `⊤`. -/
@[mk_iff] class IsSimpleSubobject (X : C) extends
  IsSimpleOrder (Subobject X)

theorem IsSimpleSubobject.congr {X Y : C} (e : X ≅ Y) [IsSimpleSubobject X] :
    IsSimpleSubobject Y where
  __ := (Subobject.mapIsoToOrderIso e.symm).isSimpleOrder

theorem IsSimpleSubobject_iff_isAtom {X : C} {x : Subobject X} :
    IsSimpleSubobject (x : C) ↔ IsAtom x := by
  rw [← Set.isSimpleOrder_Iic_iff_isAtom, isSimpleSubobject_iff]
  exact x.subobjectOrderIso.isSimpleOrder_iff

theorem IsSimpleSubobject_iff_isCoatom {X : C} {x : Subobject X} :
    IsSimpleSubobject (cokernel x.arrow) ↔ IsCoatom x := by
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom, isSimpleSubobject_iff]
  exact (Abelian.Subobject.cokernelOrderIso _).isSimpleOrder_iff

theorem IsSimpleSubobject_iff_iso {X Y : C} (e : X ≅ Y) :
    IsSimpleSubobject X ↔ IsSimpleSubobject Y :=
  ⟨fun _ ↦ IsSimpleSubobject.congr e, fun _ ↦ IsSimpleSubobject.congr e.symm⟩

theorem covBy_iff_cokernel_is_simple {X : C} {A B : Subobject X} (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleSubobject (cokernel (A.ofLE B hAB)) := by
  set f : Subobject (B : C) ≃o Set.Iic B := B.subobjectOrderIso with hf
  rw [covBy_iff_coatom_Iic hAB]
  have : (cokernel (A.ofLE B hAB)) ≅ cokernel ((Subobject.mk (A.ofLE B hAB)).arrow) :=
    cokernel.mapIso _ _ ((underlyingIso _).symm) (Iso.refl _) (by simp)
  rw [IsSimpleSubobject_iff_iso this]
  rw [IsSimpleSubobject_iff_isCoatom, ← OrderIso.isCoatom_iff f, hf]
  dsimp [subobjectOrderIso]
  have : Subobject.mk ((Subobject.mk (A.ofLE B hAB)).arrow ≫ B.arrow) = A := by
    refine mk_eq_of_comm ((Subobject.mk (A.ofLE B hAB)).arrow ≫ B.arrow) ?_ ?_
    · exact underlyingIso (A.ofLE B hAB)
    · rw [← underlyingIso_hom_comp_eq_mk, Category.assoc, Iso.cancel_iso_hom_left, ofLE_arrow]
  simp [this]

end IsSimpleSubobject

end CategoryTheory.Abelian.Subobject
