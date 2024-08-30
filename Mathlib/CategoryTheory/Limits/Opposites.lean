/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.DiscreteCategory

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We also give special cases for (co)products,
(co)equalizers, and pullbacks / pushouts.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

@[deprecated (since := "2024-03-26")] alias isLimitCoconeOp := IsColimit.op
@[deprecated (since := "2024-03-26")] alias isColimitConeOp := IsLimit.op
@[deprecated (since := "2024-03-26")] alias isLimitCoconeUnop := IsColimit.unop
@[deprecated (since := "2024-03-26")] alias isColimitConeUnop := IsLimit.unop

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps]
def isLimitConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneLeftOpOfCocone c) where
  lift s := (hc.desc (coconeOfConeLeftOp s)).unop
  fac s j :=
    Quiver.Hom.op_inj <| by
      simp only [coneLeftOpOfCocone_π_app, op_comp, Quiver.Hom.op_unop, IsColimit.fac,
        coconeOfConeLeftOp_ι_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac, coconeOfConeLeftOp_ι_app] using w (op j)

/-- Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeLeftOpOfCone c) where
  desc s := (hc.lift (coneOfCoconeLeftOp s)).unop
  fac s j :=
    Quiver.Hom.op_inj <| by
      simp only [coconeLeftOpOfCone_ι_app, op_comp, Quiver.Hom.op_unop, IsLimit.fac,
        coneOfCoconeLeftOp_π_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac, coneOfCoconeLeftOp_π_app] using w (op j)

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneRightOpOfCocone c) where
  lift s := (hc.desc (coconeOfConeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using w (unop j)

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeRightOpOfCone c) where
  desc s := (hc.lift (coneOfCoconeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using w (unop j)

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps]
def isLimitConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneUnopOfCocone c) where
  lift s := (hc.desc (coconeOfConeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using w (unop j)

/-- Turn a limit of `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit of `F.unop : J ⥤ C`. -/
@[simps]
def isColimitCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeUnopOfCone c) where
  desc s := (hc.lift (coneOfCoconeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using w (unop j)

/-- Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeLeftOp c) where
  lift s := (hc.desc (coconeLeftOpOfCone s)).op
  fac s j :=
    Quiver.Hom.unop_inj <| by
      simp only [coneOfCoconeLeftOp_π_app, unop_comp, Quiver.Hom.unop_op, IsColimit.fac,
        coconeLeftOpOfCone_ι_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac, coneOfCoconeLeftOp_π_app] using w (unop j)

/-- Turn a limit of `F.leftOp : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeLeftOp c) where
  desc s := (hc.lift (coneLeftOpOfCocone s)).op
  fac s j :=
    Quiver.Hom.unop_inj <| by
      simp only [coconeOfConeLeftOp_ι_app, unop_comp, Quiver.Hom.unop_op, IsLimit.fac,
        coneLeftOpOfCocone_π_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac, coconeOfConeLeftOp_ι_app] using w (unop j)

/-- Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isLimitConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeRightOp c) where
  lift s := (hc.desc (coconeRightOpOfCone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using w (op j)

/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeRightOp c) where
  desc s := (hc.lift (coneRightOpOfCocone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using w (op j)

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsColimit c) :
    IsLimit (coneOfCoconeUnop c) where
  lift s := (hc.desc (coconeUnopOfCone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using w (op j)

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsLimit c) :
    IsColimit (coconeOfConeUnop c) where
  desc s := (hc.lift (coneUnopOfCocone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using w (op j)

/-- If `F.leftOp : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
theorem hasLimit_of_hasColimit_leftOp (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeLeftOp (colimit.cocone F.leftOp)
      isLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }

theorem hasLimit_of_hasColimit_op (F : J ⥤ C) [HasColimit F.op] : HasLimit F :=
  HasLimit.mk
    { cone := (colimit.cocone F.op).unop
      isLimit := (colimit.isColimit _).unop }

theorem hasLimit_op_of_hasColimit (F : J ⥤ C) [HasColimit F] : HasLimit F.op :=
  HasLimit.mk
    { cone := (colimit.cocone F).op
      isLimit := (colimit.isColimit _).op }

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem hasLimitsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] :
    HasLimitsOfShape J Cᵒᵖ :=
  { has_limit := fun F => hasLimit_of_hasColimit_leftOp F }

theorem hasLimitsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasLimitsOfShape J C :=
  { has_limit := fun F => hasLimit_of_hasColimit_op F }

attribute [local instance] hasLimitsOfShape_op_of_hasColimitsOfShape

/-- If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
instance hasLimits_op_of_hasColimits [HasColimits C] : HasLimits Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩

theorem hasLimits_of_hasColimits_op [HasColimits Cᵒᵖ] : HasLimits C :=
  { has_limits_of_shape := fun _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

instance has_cofiltered_limits_op_of_has_filtered_colimits [HasFilteredColimitsOfSize.{v₂, u₂} C] :
    HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ where
  HasLimitsOfShape _ _ _ := hasLimitsOfShape_op_of_hasColimitsOfShape

theorem has_cofiltered_limits_of_has_filtered_colimits_op [HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasCofilteredLimitsOfSize.{v₂, u₂} C :=
  { HasLimitsOfShape := fun _ _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

/-- If `F.leftOp : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
theorem hasColimit_of_hasLimit_leftOp (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeLeftOp (limit.cone F.leftOp)
      isColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }

theorem hasColimit_of_hasLimit_op (F : J ⥤ C) [HasLimit F.op] : HasColimit F :=
  HasColimit.mk
    { cocone := (limit.cone F.op).unop
      isColimit := (limit.isLimit _).unop }

theorem hasColimit_op_of_hasLimit (F : J ⥤ C) [HasLimit F] : HasColimit F.op :=
  HasColimit.mk
    { cocone := (limit.cone F).op
      isColimit := (limit.isLimit _).op }

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
instance hasColimitsOfShape_op_of_hasLimitsOfShape [HasLimitsOfShape Jᵒᵖ C] :
    HasColimitsOfShape J Cᵒᵖ where has_colimit F := hasColimit_of_hasLimit_leftOp F

theorem hasColimitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasColimitsOfShape J C :=
  { has_colimit := fun F => hasColimit_of_hasLimit_op F }

/-- If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
instance hasColimits_op_of_hasLimits [HasLimits C] : HasColimits Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩

theorem hasColimits_of_hasLimits_op [HasLimits Cᵒᵖ] : HasColimits C :=
  { has_colimits_of_shape := fun _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

instance has_filtered_colimits_op_of_has_cofiltered_limits [HasCofilteredLimitsOfSize.{v₂, u₂} C] :
    HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ where HasColimitsOfShape _ _ _ := inferInstance

theorem has_filtered_colimits_of_has_cofiltered_limits_op [HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasFilteredColimitsOfSize.{v₂, u₂} C :=
  { HasColimitsOfShape := fun _ _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

variable (X : Type v₂)

/-- If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
instance hasCoproductsOfShape_opposite [HasProductsOfShape X C] : HasCoproductsOfShape X Cᵒᵖ := by
  haveI : HasLimitsOfShape (Discrete X)ᵒᵖ C :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  infer_instance

theorem hasCoproductsOfShape_of_opposite [HasProductsOfShape X Cᵒᵖ] : HasCoproductsOfShape X C :=
  haveI : HasLimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasColimitsOfShape_of_hasLimitsOfShape_op

/-- If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
instance hasProductsOfShape_opposite [HasCoproductsOfShape X C] : HasProductsOfShape X Cᵒᵖ := by
  haveI : HasColimitsOfShape (Discrete X)ᵒᵖ C :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  infer_instance

theorem hasProductsOfShape_of_opposite [HasCoproductsOfShape X Cᵒᵖ] : HasProductsOfShape X C :=
  haveI : HasColimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_of_hasColimitsOfShape_op

instance hasProducts_opposite [HasCoproducts.{v₂} C] : HasProducts.{v₂} Cᵒᵖ := fun _ =>
  inferInstance

theorem hasProducts_of_opposite [HasCoproducts.{v₂} Cᵒᵖ] : HasProducts.{v₂} C := fun X =>
  hasProductsOfShape_of_opposite X

instance hasCoproducts_opposite [HasProducts.{v₂} C] : HasCoproducts.{v₂} Cᵒᵖ := fun _ =>
  inferInstance

theorem hasCoproducts_of_opposite [HasProducts.{v₂} Cᵒᵖ] : HasCoproducts.{v₂} C := fun X =>
  hasCoproductsOfShape_of_opposite X

instance hasFiniteCoproducts_opposite [HasFiniteProducts C] : HasFiniteCoproducts Cᵒᵖ where
  out _ := Limits.hasCoproductsOfShape_opposite _

theorem hasFiniteCoproducts_of_opposite [HasFiniteProducts Cᵒᵖ] : HasFiniteCoproducts C :=
  { out := fun _ => hasCoproductsOfShape_of_opposite _ }

instance hasFiniteProducts_opposite [HasFiniteCoproducts C] : HasFiniteProducts Cᵒᵖ where
  out _ := inferInstance

theorem hasFiniteProducts_of_opposite [HasFiniteCoproducts Cᵒᵖ] : HasFiniteProducts C :=
  { out := fun _ => hasProductsOfShape_of_opposite _ }

section OppositeCoproducts

variable {α : Type*} {Z : α → C}

section
variable [HasCoproduct Z]

instance : HasLimit (Discrete.functor Z).op := hasLimit_op_of_hasColimit (Discrete.functor Z)

instance : HasLimit ((Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op) :=
  hasLimitEquivalenceComp (Discrete.opposite α).symm

instance : HasProduct (op <| Z ·) := hasLimitOfIso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ ↦ by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·))

/-- A `Cofan` gives a `Fan` in the opposite category. -/
@[simp]
def Cofan.op (c : Cofan Z) : Fan (op <| Z ·) := Fan.mk _ (fun a ↦ (c.inj a).op)

/-- If a `Cofan` is colimit, then its opposite is limit. -/
def Cofan.IsColimit.op {c : Cofan Z} (hc : IsColimit c) : IsLimit c.op := by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ ↦ Iso.refl _)
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv e _).2
    (IsLimit.whiskerEquivalence hc.op (Discrete.opposite α).symm))
    (Cones.ext (Iso.refl _) (fun ⟨a⟩ ↦ ?_))
  dsimp
  erw [Category.id_comp, Category.comp_id]
  rfl

/--
The canonical isomorphism from the opposite of an abstract coproduct to the corresponding product
in the opposite category.
-/
def opCoproductIsoProduct' {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) : op c.pt ≅ f.pt :=
  IsLimit.conePointUniqueUpToIso (Cofan.IsColimit.op hc) hf

variable (Z) in
/--
The canonical isomorphism from the opposite of the coproduct to the product in the opposite
category.
-/
def opCoproductIsoProduct :
    op (∐ Z) ≅ ∏ᶜ (op <| Z ·) :=
  opCoproductIsoProduct' (coproductIsCoproduct Z) (productIsProduct (op <| Z ·))

end

theorem opCoproductIsoProduct'_inv_comp_inj {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (b : α) :
    (opCoproductIsoProduct' hc hf).inv ≫ (c.inj b).op = f.proj b :=
  IsLimit.conePointUniqueUpToIso_inv_comp (Cofan.IsColimit.op hc) hf ⟨b⟩

theorem opCoproductIsoProduct'_comp_self {c c' : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hc' : IsColimit c') (hf : IsLimit f) :
    (opCoproductIsoProduct' hc hf).hom ≫ (opCoproductIsoProduct' hc' hf).inv =
    (hc.coconePointUniqueUpToIso hc').op.inv := by
  apply Quiver.Hom.unop_inj
  apply hc'.hom_ext
  intro ⟨j⟩
  change c'.inj _ ≫ _ = _
  simp only [unop_op, unop_comp, Discrete.functor_obj, const_obj_obj, Iso.op_inv,
    Quiver.Hom.unop_op, IsColimit.comp_coconePointUniqueUpToIso_inv]
  apply Quiver.Hom.op_inj
  simp only [op_comp, op_unop, Quiver.Hom.op_unop, Category.assoc,
    opCoproductIsoProduct'_inv_comp_inj]
  rw [← opCoproductIsoProduct'_inv_comp_inj hc hf]
  simp only [Iso.hom_inv_id_assoc]
  rfl

variable (Z) in
theorem opCoproductIsoProduct_inv_comp_ι [HasCoproduct Z] (b : α) :
    (opCoproductIsoProduct Z).inv ≫ (Sigma.ι Z b).op = Pi.π (op <| Z ·) b :=
  opCoproductIsoProduct'_inv_comp_inj _ _ b

theorem desc_op_comp_opCoproductIsoProduct'_hom {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (c' : Cofan Z) :
    (hc.desc c').op ≫ (opCoproductIsoProduct' hc hf).hom = hf.lift c'.op := by
  refine (Iso.eq_comp_inv _).mp (Quiver.Hom.unop_inj (hc.hom_ext (fun ⟨j⟩ ↦ Quiver.Hom.op_inj ?_)))
  simp only [unop_op, Discrete.functor_obj, const_obj_obj, Quiver.Hom.unop_op, IsColimit.fac,
    Cofan.op, unop_comp, op_comp, op_unop, Quiver.Hom.op_unop, Category.assoc]
  erw [opCoproductIsoProduct'_inv_comp_inj, IsLimit.fac]
  rfl

theorem desc_op_comp_opCoproductIsoProduct_hom [HasCoproduct Z] {X : C} (π : (a : α) → Z a ⟶ X) :
    (Sigma.desc π).op ≫ (opCoproductIsoProduct Z).hom = Pi.lift (fun a ↦ (π a).op) := by
  convert desc_op_comp_opCoproductIsoProduct'_hom (coproductIsCoproduct Z)
    (productIsProduct (op <| Z ·)) (Cofan.mk _ π)
  · ext; simp [Sigma.desc, coproductIsCoproduct]
  · ext; simp [Pi.lift, productIsProduct]

end OppositeCoproducts

section OppositeProducts

variable {α : Type*} {Z : α → C}

section
variable [HasProduct Z]

instance : HasColimit (Discrete.functor Z).op := hasColimit_op_of_hasLimit (Discrete.functor Z)

instance : HasColimit ((Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op) :=
  hasColimit_equivalence_comp (Discrete.opposite α).symm

instance : HasCoproduct (op <| Z ·) := hasColimitOfIso
  ((Discrete.natIsoFunctor ≪≫ Discrete.natIso (fun _ ↦ by rfl)) :
    (Discrete.opposite α).inverse ⋙ (Discrete.functor Z).op ≅
    Discrete.functor (op <| Z ·)).symm

/-- A `Fan` gives a `Cofan` in the opposite category. -/
@[simp]
def Fan.op (f : Fan Z) : Cofan (op <| Z ·) := Cofan.mk _ (fun a ↦ (f.proj a).op)

/-- If a `Fan` is limit, then its opposite is colimit. -/
def Fan.IsLimit.op {f : Fan Z} (hf : IsLimit f) : IsColimit f.op := by
  let e : Discrete.functor (Opposite.op <| Z ·) ≅ (Discrete.opposite α).inverse ⋙
    (Discrete.functor Z).op := Discrete.natIso (fun _ ↦ Iso.refl _)
  refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e _).2
    (IsColimit.whiskerEquivalence hf.op (Discrete.opposite α).symm))
    (Cocones.ext (Iso.refl _) (fun ⟨a⟩ ↦ ?_))
  dsimp
  erw [Category.id_comp, Category.comp_id]
  rfl

/--
The canonical isomorphism from the opposite of an abstract product to the corresponding coproduct
in the opposite category.
-/
def opProductIsoCoproduct' {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) : op f.pt ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso (Fan.IsLimit.op hf) hc

variable (Z) in
/--
The canonical isomorphism from the opposite of the product to the coproduct in the opposite
category.
-/
def opProductIsoCoproduct :
    op (∏ᶜ Z) ≅ ∐ (op <| Z ·) :=
  opProductIsoCoproduct' (productIsProduct Z) (coproductIsCoproduct (op <| Z ·))

end

theorem proj_comp_opProductIsoCoproduct'_hom {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) (b : α) :
    (f.proj b).op ≫ (opProductIsoCoproduct' hf hc).hom = c.inj b :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (Fan.IsLimit.op hf) hc ⟨b⟩

theorem opProductIsoCoproduct'_comp_self {f f' : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hf' : IsLimit f') (hc : IsColimit c) :
    (opProductIsoCoproduct' hf hc).hom ≫ (opProductIsoCoproduct' hf' hc).inv =
    (hf.conePointUniqueUpToIso hf').op.inv := by
  apply Quiver.Hom.unop_inj
  apply hf.hom_ext
  intro ⟨j⟩
  change _ ≫ f.proj _ = _
  simp only [unop_op, unop_comp, Category.assoc, Discrete.functor_obj, Iso.op_inv,
    Quiver.Hom.unop_op, IsLimit.conePointUniqueUpToIso_inv_comp]
  apply Quiver.Hom.op_inj
  simp only [op_comp, op_unop, Quiver.Hom.op_unop, proj_comp_opProductIsoCoproduct'_hom]
  rw [← proj_comp_opProductIsoCoproduct'_hom hf' hc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

variable (Z) in
theorem π_comp_opProductIsoCoproduct_hom [HasProduct Z] (b : α) :
    (Pi.π Z b).op ≫ (opProductIsoCoproduct Z).hom = Sigma.ι (op <| Z ·) b :=
  proj_comp_opProductIsoCoproduct'_hom _ _ b

theorem opProductIsoCoproduct'_inv_comp_lift {f : Fan Z} {c : Cofan (op <| Z ·)}
    (hf : IsLimit f) (hc : IsColimit c) (f' : Fan Z) :
    (opProductIsoCoproduct' hf hc).inv ≫ (hf.lift f').op = hc.desc f'.op := by
  refine (Iso.inv_comp_eq _).mpr (Quiver.Hom.unop_inj (hf.hom_ext (fun ⟨j⟩ ↦ Quiver.Hom.op_inj ?_)))
  simp only [Discrete.functor_obj, unop_op, Quiver.Hom.unop_op, IsLimit.fac, Fan.op, unop_comp,
    Category.assoc, op_comp, op_unop, Quiver.Hom.op_unop]
  erw [← Category.assoc, proj_comp_opProductIsoCoproduct'_hom, IsColimit.fac]
  rfl

theorem opProductIsoCoproduct_inv_comp_lift [HasProduct Z] {X : C} (π : (a : α) → X ⟶ Z a) :
    (opProductIsoCoproduct Z).inv ≫ (Pi.lift π).op  = Sigma.desc (fun a ↦ (π a).op) := by
  convert opProductIsoCoproduct'_inv_comp_lift (productIsProduct Z)
    (coproductIsCoproduct (op <| Z ·)) (Fan.mk _ π)
  · ext; simp [Pi.lift, productIsProduct]
  · ext; simp [Sigma.desc, coproductIsCoproduct]

end OppositeProducts

section BinaryProducts

variable {A B : C} [HasBinaryProduct A B]

instance : HasBinaryCoproduct (op A) (op B) := by
  have : HasProduct fun x ↦ (WalkingPair.casesOn x A B : C) := ‹_›
  show HasCoproduct _
  convert inferInstanceAs (HasCoproduct fun x ↦ op (WalkingPair.casesOn x A B : C)) with x
  cases x <;> rfl

variable (A B) in
/--
The canonical isomorphism from the opposite of the binary product to the coproduct in the opposite
category.
-/
def opProdIsoCoprod : op (A ⨯ B) ≅ (op A ⨿ op B) where
  hom := (prod.lift coprod.inl.unop coprod.inr.unop).op
  inv := coprod.desc prod.fst.op prod.snd.op
  hom_inv_id := by
    apply Quiver.Hom.unop_inj
    ext <;>
    · simp only [limit.lift_π]
      apply Quiver.Hom.op_inj
      simp
  inv_hom_id := by
    ext <;>
    · simp only [colimit.ι_desc_assoc]
      apply Quiver.Hom.unop_inj
      simp

@[reassoc (attr := simp)]
lemma fst_opProdIsoCoprod_hom : prod.fst.op ≫ (opProdIsoCoprod A B).hom = coprod.inl := by
  rw [opProdIsoCoprod, ← op_comp, prod.lift_fst, Quiver.Hom.op_unop]

@[reassoc (attr := simp)]
lemma snd_opProdIsoCoprod_hom : prod.snd.op ≫ (opProdIsoCoprod A B).hom = coprod.inr := by
  rw [opProdIsoCoprod, ← op_comp, prod.lift_snd, Quiver.Hom.op_unop]

@[reassoc (attr := simp)]
lemma inl_opProdIsoCoprod_inv : coprod.inl ≫ (opProdIsoCoprod A B).inv = prod.fst.op := by
  rw [Iso.comp_inv_eq, fst_opProdIsoCoprod_hom]

@[reassoc (attr := simp)]
lemma inr_opProdIsoCoprod_inv : coprod.inr ≫ (opProdIsoCoprod A B).inv = prod.snd.op := by
  rw [Iso.comp_inv_eq, snd_opProdIsoCoprod_hom]

@[reassoc (attr := simp)]
lemma opProdIsoCoprod_hom_fst : (opProdIsoCoprod A B).hom.unop ≫ prod.fst = coprod.inl.unop := by
  simp [opProdIsoCoprod]

@[reassoc (attr := simp)]
lemma opProdIsoCoprod_hom_snd : (opProdIsoCoprod A B).hom.unop ≫ prod.snd = coprod.inr.unop := by
  simp [opProdIsoCoprod]

@[reassoc (attr := simp)]
lemma opProdIsoCoprod_inv_inl : (opProdIsoCoprod A B).inv.unop ≫ coprod.inl.unop = prod.fst := by
  rw [← unop_comp, inl_opProdIsoCoprod_inv, Quiver.Hom.unop_op]

@[reassoc (attr := simp)]
lemma opProdIsoCoprod_inv_inr : (opProdIsoCoprod A B).inv.unop ≫ coprod.inr.unop = prod.snd := by
  rw [← unop_comp, inr_opProdIsoCoprod_inv, Quiver.Hom.unop_op]

end BinaryProducts

instance hasEqualizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ := by
  haveI : HasColimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  infer_instance

instance hasCoequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ := by
  haveI : HasLimitsOfShape WalkingParallelPairᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingParallelPairOpEquiv
  infer_instance

instance hasFiniteColimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ :=
  ⟨fun _ _ _ => inferInstance⟩

instance hasFiniteLimits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ :=
  ⟨fun _ _ _ => inferInstance⟩

instance hasPullbacks_opposite [HasPushouts C] : HasPullbacks Cᵒᵖ := by
  haveI : HasColimitsOfShape WalkingCospanᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingCospanOpEquiv.symm
  apply hasLimitsOfShape_op_of_hasColimitsOfShape

instance hasPushouts_opposite [HasPullbacks C] : HasPushouts Cᵒᵖ := by
  haveI : HasLimitsOfShape WalkingSpanᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingSpanOpEquiv.symm
  infer_instance

/-- The canonical isomorphism relating `Span f.op g.op` and `(Cospan f g).op` -/
@[simps!]
def spanOp {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.op g.op ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
  NatIso.ofComponents (by rintro (_ | _ | _) <;> rfl)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> aesop_cat)

/-- The canonical isomorphism relating `(Cospan f g).op` and `Span f.op g.op` -/
@[simps!]
def opCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).op ≅ walkingCospanOpEquiv.functor ⋙ span f.op g.op :=
  calc
    (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op := by rfl
    _ ≅ (walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse) ⋙ (cospan f g).op :=
      (isoWhiskerRight walkingCospanOpEquiv.unitIso _)
    _ ≅ walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
      (Functor.associator _ _ _)
    _ ≅ walkingCospanOpEquiv.functor ⋙ span f.op g.op := isoWhiskerLeft _ (spanOp f g).symm

/-- The canonical isomorphism relating `Cospan f.op g.op` and `(Span f g).op` -/
@[simps!]
def cospanOp {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.op g.op ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
  NatIso.ofComponents (by rintro (_ | _ | _) <;> rfl)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> aesop_cat)

/-- The canonical isomorphism relating `(Span f g).op` and `Cospan f.op g.op` -/
@[simps!]
def opSpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    (span f g).op ≅ walkingSpanOpEquiv.functor ⋙ cospan f.op g.op :=
  calc
    (span f g).op ≅ 𝟭 _ ⋙ (span f g).op := by rfl
    _ ≅ (walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse) ⋙ (span f g).op :=
      (isoWhiskerRight walkingSpanOpEquiv.unitIso _)
    _ ≅ walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
      (Functor.associator _ _ _)
    _ ≅ walkingSpanOpEquiv.functor ⋙ cospan f.op g.op := isoWhiskerLeft _ (cospanOp f g).symm

namespace PushoutCocone

-- Porting note: it was originally @[simps (config := lemmasOnly)]
/-- The obvious map `PushoutCocone f g → PullbackCone f.unop g.unop` -/
@[simps!]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    PullbackCone f.unop g.unop :=
  Cocone.unop
    ((Cocones.precompose (opCospan f.unop g.unop).hom).obj
      (Cocone.whisker walkingCospanOpEquiv.functor c))

-- Porting note (#10618): removed simp attribute as the equality can already be obtained by simp
theorem unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.fst = c.inl.unop := by simp

-- Porting note (#10618): removed simp attribute as the equality can already be obtained by simp
theorem unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.snd = c.inr.unop := by aesop_cat

-- Porting note: it was originally @[simps (config := lemmasOnly)]
/-- The obvious map `PushoutCocone f.op g.op → PullbackCone f g` -/
@[simps!]
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackCone f.op g.op :=
  (Cones.postcompose (cospanOp f g).symm.hom).obj
    (Cone.whisker walkingSpanOpEquiv.inverse (Cocone.op c))

-- Porting note (#10618): removed simp attribute as the equality can already be obtained by simp
theorem op_fst {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.op.fst = c.inl.op := by aesop_cat

-- Porting note (#10618): removed simp attribute as the equality can already be obtained by simp
theorem op_snd {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.op.snd = c.inr.op := by aesop_cat

end PushoutCocone

namespace PullbackCone

-- Porting note: it was originally @[simps (config := lemmasOnly)]
/-- The obvious map `PullbackCone f g → PushoutCocone f.unop g.unop` -/
@[simps!]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    PushoutCocone f.unop g.unop :=
  Cone.unop
    ((Cones.postcompose (opSpan f.unop g.unop).symm.hom).obj
      (Cone.whisker walkingSpanOpEquiv.functor c))

-- Porting note (#10618): removed simp attribute as the equality can already be obtained by simp
theorem unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inl = c.fst.unop := by aesop_cat

-- Porting note (#10618): removed simp attribute as the equality can already be obtained by simp
theorem unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inr = c.snd.unop := by aesop_cat

/-- The obvious map `PullbackCone f g → PushoutCocone f.op g.op` -/
@[simps!]
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCocone f.op g.op :=
  (Cocones.precompose (spanOp f g).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.inverse (Cone.op c))

-- Porting note (#10618): removed simp attribute as the equality can already be obtained by simp
theorem op_inl {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.op.inl = c.fst.op := by aesop_cat

-- Porting note (#10618): removed simp attribute as the equality can already be obtained by simp
theorem op_inr {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.op.inr = c.snd.op := by aesop_cat

/-- If `c` is a pullback cone, then `c.op.unop` is isomorphic to `c`. -/
def opUnop {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.unop ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

/-- If `c` is a pullback cone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOp {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.unop.op ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

end PullbackCone

namespace PushoutCocone

/-- If `c` is a pushout cocone, then `c.op.unop` is isomorphic to `c`. -/
def opUnop {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.unop ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

/-- If `c` is a pushout cocone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.unop.op ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

/-- A pushout cone is a colimit cocone if and only if the corresponding pullback cone
in the opposite category is a limit cone. -/
def isColimitEquivIsLimitOp {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.op := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnop).toFun
      (((IsLimit.postcomposeHomEquiv _ _).invFun
        ((IsLimit.whiskerEquivalenceEquiv _).toFun h)).unop)

/-- A pushout cone is a colimit cocone in `Cᵒᵖ` if and only if the corresponding pullback cone
in `C` is a limit cone. -/
def isColimitEquivIsLimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.unop := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv _).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOp).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingCospanOpEquiv.symm).toFun h.op))

end PushoutCocone

namespace PullbackCone

/-- A pullback cone is a limit cone if and only if the corresponding pushout cocone
in the opposite category is a colimit cocone. -/
def isLimitEquivIsColimitOp {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.opUnop).symm.trans c.op.isColimitEquivIsLimitUnop.symm

/-- A pullback cone is a limit cone in `Cᵒᵖ` if and only if the corresponding pushout cocone
in `C` is a colimit cocone. -/
def isLimitEquivIsColimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unopOp).symm.trans c.unop.isColimitEquivIsLimitOp.symm

end PullbackCone

section Pullback

open Opposite

/-- The pullback of `f` and `g` in `C` is isomorphic to the pushout of
`f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable def pullbackIsoUnopPushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g]
    [HasPushout f.op g.op] : pullback f g ≅ unop (pushout f.op g.op) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitUnop _) (colimit.isColimit (span f.op g.op)))

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.fst f g =
      (pushout.inl _ _ : _ ⟶ pushout f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := X })])

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.snd f g =
      (pushout.inr _ _ : _ ⟶ pushout f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := Y })])

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_hom_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    pushout.inl _ _ ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.fst f g).op := by
  apply Quiver.Hom.unop_inj
  dsimp
  rw [← pullbackIsoUnopPushout_inv_fst, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
theorem pullbackIsoUnopPushout_hom_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] : pushout.inr _ _ ≫ (pullbackIsoUnopPushout f g).hom.op =
    (pullback.snd f g).op := by
  apply Quiver.Hom.unop_inj
  dsimp
  rw [← pullbackIsoUnopPushout_inv_snd, Iso.hom_inv_id_assoc]

end Pullback

section Pushout

/-- The pushout of `f` and `g` in `C` is isomorphic to the pullback of
 `f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable def pushoutIsoUnopPullback {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g]
    [HasPullback f.op g.op] : pushout f g ≅ unop (pullback f.op g.op) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitUnop _) (limit.isLimit (cospan f.op g.op)))

@[reassoc (attr := simp)]
theorem pushoutIsoUnopPullback_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    pushout.inl _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.fst f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[reassoc (attr := simp)]
theorem pushoutIsoUnopPullback_inr_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    pushout.inr _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.snd f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
theorem pushoutIsoUnopPullback_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.fst f.op g.op = (pushout.inl f g).op := by
  apply Quiver.Hom.unop_inj
  dsimp
  rw [← pushoutIsoUnopPullback_inl_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[simp]
theorem pushoutIsoUnopPullback_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.snd f.op g.op = (pushout.inr f g).op := by
  apply Quiver.Hom.unop_inj
  dsimp
  rw [← pushoutIsoUnopPullback_inr_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Pushout

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- A colimit cokernel cofork gives a limit kernel fork in the opposite category -/
def CokernelCofork.IsColimit.ofπOp {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.op (show p.op ≫ f.op = 0 by rw [← op_comp, w, op_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.unop (Quiver.Hom.op_inj hx))).op)
    (fun x hx => Quiver.Hom.unop_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.unop_op, Cofork.IsColimit.π_desc] using Quiver.Hom.op_inj hb)))

/-- A colimit cokernel cofork in the opposite category gives a limit kernel fork
in the original category -/
def CokernelCofork.IsColimit.ofπUnop {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.unop (show p.unop ≫ f.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun x hx => Quiver.Hom.op_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.op_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.op_unop, Cofork.IsColimit.π_desc] using Quiver.Hom.unop_inj hb)))

/-- A limit kernel fork gives a colimit cokernel cofork in the opposite category -/
def KernelFork.IsLimit.ofιOp {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.op
      (show f.op ≫ i.op = 0 by rw [← op_comp, w, op_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.unop (Quiver.Hom.op_inj hx))).op)
    (fun x hx => Quiver.Hom.unop_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.unop_op, Fork.IsLimit.lift_ι] using Quiver.Hom.op_inj hb)))

/-- A limit kernel fork in the opposite category gives a colimit cokernel cofork
in the original category -/
def KernelFork.IsLimit.ofιUnop {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.unop
      (show f.unop ≫ i.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun x hx => Quiver.Hom.op_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.op_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.op_unop, Fork.IsLimit.lift_ι] using Quiver.Hom.unop_inj hb)))

end HasZeroMorphisms

end CategoryTheory.Limits
