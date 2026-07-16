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

This file contains numerous results about subobjects which are unique to abelian categories. In
particular, `exists_eq_kernelSubobject` and `pullback_eq_kernelSubobject` specialize
`Subobject.«exists»` and `Subobject.pullback` API to the abelian case.

## Main results

* subobjects and quotient objects of an object `X` are order-isomorphic via taking kernels and
  cokernels
* a correspondence theorem: Given a subobject `Y` of `X`, `Abelian.Subobject.cokernelOrderIso` is
  an order-isomorphism between subobjects of `cokernel (Y ↪ X)` and subobjects of `X`
  containing `Y`.
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

lemma exists_eq_kernelSubobject (X' : Subobject X) :
    («exists» f).obj X' = kernelSubobject (cokernel.π (X'.arrow ≫ f)) := by
  rw [exists_eq_imageSubobject, ← imageSubobject_eq_kernelSubobject]

lemma pullback_eq_kernelSubobject (Y' : Subobject Y) :
    (Subobject.pullback f).obj Y' = kernelSubobject (f ≫ cokernel.π Y'.arrow) := by
  slice_lhs 0 1 => rw [← mk_arrow Y', ← imageSubobject_mono Y'.arrow,
    imageSubobject_eq_kernelSubobject, pullback_kernelSubobject]

lemma pullback_mk_eq_kernelSubobject {A : C} (g : A ⟶ Y) [Mono g] :
    (Subobject.pullback f).obj (Subobject.mk g) = kernelSubobject (f ≫ cokernel.π g) := by
  rw [← imageSubobject_mono, imageSubobject_eq_kernelSubobject, pullback_kernelSubobject]

/-- Direct image satisfies Frobenius reciprocity with inverse image in an abelian category. -/
lemma directImage_inf_inverseImage (X' : Subobject X) (Y' : Subobject Y) :
    (directImage f).obj (X' ⊓ (inverseImage f).obj Y') = (directImage f).obj X' ⊓ Y' := by
  rw [directImage_eq_exists, inverseImage_eq_pullback, directImage_eq_exists]
  exact Regular.exists_inf_pullback_eq_exists_inf f X' Y'

theorem exists_pullback_eq_self_of_epi [Epi f] (Y' : Subobject Y) :
    («exists» f).obj ((Subobject.pullback f).obj Y') = Y' := by
  rw [exists_eq_imageSubobject, ← (isPullback f Y').w]
  let : Epi (pullbackπ f Y') := epi_fst_of_isLimit _ _ (isPullback f Y').isLimit
  let : StrongEpi (pullbackπ f Y') := strongEpi_of_epi _
  rw [imageSubobject_epi_comp, imageSubobject_mono, mk_arrow]

theorem pullback_le_pullback_iff_of_epi (Y₁ Y₂ : Subobject Y) [Epi f] :
    (Subobject.pullback f).obj Y₁ ≤ (Subobject.pullback f).obj Y₂ ↔ Y₁ ≤ Y₂ := by
  constructor
  · intro h
    rw [← exists_pullback_eq_self_of_epi f Y₁, ← exists_pullback_eq_self_of_epi f Y₂]
    exact («exists» f).monotone h
  · intro h
    exact (Subobject.pullback f).monotone h

lemma pullback_exists_eq_self_of_epi [Epi f] (X' : Subobject X) (h : kernelSubobject f ≤ X') :
    (Subobject.pullback f).obj ((«exists» f).obj X') = X' := by
  let d := epiDesc f (cokernel.π X'.arrow) (by
    rw [← kernelSubobject_arrow' f, ← ofLE_arrow h]
    simp only [Category.assoc, cokernel.condition, comp_zero])
  have : Epi d := epi_of_epi_fac (comp_epiDesc f (cokernel.π X'.arrow) _)
  have hX' : (Subobject.pullback f).obj (kernelSubobject d) = X' := by
    rw [pullback_mk_eq_kernelSubobject, ← comp_isoCokernelKernel_hom d]
    simp only [← Category.assoc, d, comp_epiDesc, kernelSubobject_comp_mono]
    rw [← imageSubobject_eq_kernelSubobject, imageSubobject_mono]
    exact mk_arrow X'
  rw [← hX', exists_pullback_eq_self_of_epi]

lemma pullback_exists_eq_sup_of_epi [Epi f] (X' : Subobject X) :
    (Subobject.pullback f).obj ((«exists» f).obj X') = X' ⊔ kernelSubobject f := by
  apply le_antisymm
  · rw [← pullback_exists_eq_self_of_epi f (X' ⊔ kernelSubobject f) le_sup_right]
    exact (Subobject.pullback f).monotone ((«exists» f).monotone le_sup_left)
  · apply sup_le
    · exact (existsPullbackAdj f).gc.le_u_l X'
    · rw [pullback_eq_kernelSubobject]
      exact kernelSubobject_comp_le f _

theorem pullback_exists_eq_sup (X' : Subobject X) :
    (Subobject.pullback f).obj ((«exists» f).obj X') = X' ⊔ kernelSubobject f := by
  rw [← imageSubobject_arrow_comp f, exists_comp, pullback_comp, exists_iso_map, pullback_map_self,
    pullback_exists_eq_sup_of_epi, kernelSubobject_comp_mono]

theorem exists_pullback_eq_inf (Y' : Subobject Y) :
    («exists» f).obj ((Subobject.pullback f).obj Y') = Y' ⊓ imageSubobject f := by
  rw [← imageSubobject_arrow_comp f, exists_comp, Subobject.pullback_comp,
    exists_pullback_eq_self_of_epi, exists_pullback_eq_inf_of_mono, mk_arrow,
    imageSubobject_arrow_comp]

end

/-- Given a subobject `Y` of `X`, there is an order-isomorphism between subobjects
of `X/Y := cokernel (Y ↪ X)` and subobjects of `X` containing `Y`. -/
noncomputable
def cokernelOrderIso {X : C} (Y : Subobject X) :
    Subobject (cokernel Y.arrow) ≃o Set.Ici Y where
  toFun p := ⟨(Subobject.pullback (cokernel.π Y.arrow)).obj p, by
    rw [pullback_eq_kernelSubobject]
    exact le_kernelSubobject _ _ (by simp)⟩
  invFun q := («exists» (cokernel.π Y.arrow)).obj q
  left_inv p := exists_pullback_eq_self_of_epi (cokernel.π Y.arrow) p
  right_inv := by
    rintro ⟨q, hq : Y ≤ q⟩
    ext1
    exact pullback_exists_eq_self_of_epi _ _
      (by rwa [← imageSubobject_eq_kernelSubobject, imageSubobject_mono, mk_arrow])
  map_rel_iff' := pullback_le_pullback_iff_of_epi _ _ _

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
