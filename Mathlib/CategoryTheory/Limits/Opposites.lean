/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Floris van Doorn

! This file was ported from Lean 3 source module category_theory.limits.opposites
! leanprover-community/mathlib commit ac3ae212f394f508df43e37aa093722fa9b65d31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Filtered
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.Tactic.EquivRw

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

/-- Turn a colimit for `F : J ⥤ C` into a limit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitCoconeOp (F : J ⥤ C) {c : Cocone F} (hc : IsColimit c) : IsLimit c.op
    where
  lift s := (hc.desc s.unop).op
  fac s j := Quiver.Hom.unop_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_colimit.fac] using w (op j)
#align category_theory.limits.is_limit_cocone_op CategoryTheory.Limits.isLimitCoconeOp

/-- Turn a limit for `F : J ⥤ C` into a colimit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitConeOp (F : J ⥤ C) {c : Cone F} (hc : IsLimit c) : IsColimit c.op
    where
  desc s := (hc.lift s.unop).op
  fac s j := Quiver.Hom.unop_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_limit.fac] using w (op j)
#align category_theory.limits.is_colimit_cone_op CategoryTheory.Limits.isColimitConeOp

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps]
def isLimitConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneLeftOpOfCocone c)
    where
  lift s := (hc.desc (coconeOfConeLeftOp s)).unop
  fac s j :=
    Quiver.Hom.op_inj <| by
      simpa only [cone_left_op_of_cocone_π_app, op_comp, Quiver.Hom.op_unop, is_colimit.fac,
        cocone_of_cone_left_op_ι_app]
  uniq s m w := by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_colimit.fac, cocone_of_cone_left_op_ι_app] using w (op j)
#align category_theory.limits.is_limit_cone_left_op_of_cocone CategoryTheory.Limits.isLimitConeLeftOpOfCocone

/-- Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeLeftOpOfCone c)
    where
  desc s := (hc.lift (coneOfCoconeLeftOp s)).unop
  fac s j :=
    Quiver.Hom.op_inj <| by
      simpa only [cocone_left_op_of_cone_ι_app, op_comp, Quiver.Hom.op_unop, is_limit.fac,
        cone_of_cocone_left_op_π_app]
  uniq s m w := by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_limit.fac, cone_of_cocone_left_op_π_app] using w (op j)
#align category_theory.limits.is_colimit_cocone_left_op_of_cone CategoryTheory.Limits.isColimitCoconeLeftOpOfCone

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.right_op : J ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneRightOpOfCocone c)
    where
  lift s := (hc.desc (coconeOfConeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_colimit.fac] using w (unop j)
#align category_theory.limits.is_limit_cone_right_op_of_cocone CategoryTheory.Limits.isLimitConeRightOpOfCocone

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.right_op : J ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeRightOpOfCone c)
    where
  desc s := (hc.lift (coneOfCoconeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_limit.fac] using w (unop j)
#align category_theory.limits.is_colimit_cocone_right_op_of_cone CategoryTheory.Limits.isColimitCoconeRightOpOfCone

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps]
def isLimitConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneUnopOfCocone c)
    where
  lift s := (hc.desc (coconeOfConeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_colimit.fac] using w (unop j)
#align category_theory.limits.is_limit_cone_unop_of_cocone CategoryTheory.Limits.isLimitConeUnopOfCocone

/-- Turn a limit of `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit of `F.unop : J ⥤ C`. -/
@[simps]
def isColimitCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeUnopOfCone c)
    where
  desc s := (hc.lift (coneOfCoconeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_limit.fac] using w (unop j)
#align category_theory.limits.is_colimit_cocone_unop_of_cone CategoryTheory.Limits.isColimitCoconeUnopOfCone

/-- Turn a colimit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F : J ⥤ C`. -/
@[simps]
def isLimitCoconeUnop (F : J ⥤ C) {c : Cocone F.op} (hc : IsColimit c) : IsLimit c.unop
    where
  lift s := (hc.desc s.op).unop
  fac s j := Quiver.Hom.op_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_colimit.fac] using w (unop j)
#align category_theory.limits.is_limit_cocone_unop CategoryTheory.Limits.isLimitCoconeUnop

/-- Turn a limit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F : J ⥤ C`. -/
@[simps]
def isColimitConeUnop (F : J ⥤ C) {c : Cone F.op} (hc : IsLimit c) : IsColimit c.unop
    where
  desc s := (hc.lift s.op).unop
  fac s j := Quiver.Hom.op_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_limit.fac] using w (unop j)
#align category_theory.limits.is_colimit_cone_unop CategoryTheory.Limits.isColimitConeUnop

/-- Turn a colimit for `F.left_op : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeLeftOp c)
    where
  lift s := (hc.desc (coconeLeftOpOfCone s)).op
  fac s j :=
    Quiver.Hom.unop_inj <| by
      simpa only [cone_of_cocone_left_op_π_app, unop_comp, Quiver.Hom.unop_op, is_colimit.fac,
        cocone_left_op_of_cone_ι_app]
  uniq s m w := by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_colimit.fac, cone_of_cocone_left_op_π_app] using w (unop j)
#align category_theory.limits.is_limit_cone_of_cocone_left_op CategoryTheory.Limits.isLimitConeOfCoconeLeftOp

/-- Turn a limit of `F.left_op : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeLeftOp c)
    where
  desc s := (hc.lift (coneLeftOpOfCocone s)).op
  fac s j :=
    Quiver.Hom.unop_inj <| by
      simpa only [cocone_of_cone_left_op_ι_app, unop_comp, Quiver.Hom.unop_op, is_limit.fac,
        cone_left_op_of_cocone_π_app]
  uniq s m w := by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_limit.fac, cocone_of_cone_left_op_ι_app] using w (unop j)
#align category_theory.limits.is_colimit_cocone_of_cone_left_op CategoryTheory.Limits.isColimitCoconeOfConeLeftOp

/-- Turn a colimit for `F.right_op : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isLimitConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeRightOp c)
    where
  lift s := (hc.desc (coconeRightOpOfCone s)).unop
  fac s j := Quiver.Hom.op_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_colimit.fac] using w (op j)
#align category_theory.limits.is_limit_cone_of_cocone_right_op CategoryTheory.Limits.isLimitConeOfCoconeRightOp

/-- Turn a limit for `F.right_op : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeRightOp c)
    where
  desc s := (hc.lift (coneRightOpOfCocone s)).unop
  fac s j := Quiver.Hom.op_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_limit.fac] using w (op j)
#align category_theory.limits.is_colimit_cocone_of_cone_right_op CategoryTheory.Limits.isColimitCoconeOfConeRightOp

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsColimit c) :
    IsLimit (coneOfCoconeUnop c)
    where
  lift s := (hc.desc (coconeUnopOfCone s)).op
  fac s j := Quiver.Hom.unop_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_colimit.fac] using w (op j)
#align category_theory.limits.is_limit_cone_of_cocone_unop CategoryTheory.Limits.isLimitConeOfCoconeUnop

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsLimit c) :
    IsColimit (coconeOfConeUnop c)
    where
  desc s := (hc.lift (coneUnopOfCocone s)).op
  fac s j := Quiver.Hom.unop_inj (by simpa)
  uniq s m w := by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_limit.fac] using w (op j)
#align category_theory.limits.is_colimit_cone_of_cocone_unop CategoryTheory.Limits.isColimitConeOfCoconeUnop

/-- If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
theorem hasLimit_of_hasColimit_leftOp (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F :=
  HasLimit.mk
    { Cone := coneOfCoconeLeftOp (colimit.cocone F.leftOp)
      IsLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }
#align category_theory.limits.has_limit_of_has_colimit_left_op CategoryTheory.Limits.hasLimit_of_hasColimit_leftOp

theorem hasLimit_of_hasColimit_op (F : J ⥤ C) [HasColimit F.op] : HasLimit F :=
  HasLimit.mk
    { Cone := (colimit.cocone F.op).unop
      IsLimit := isLimitCoconeUnop _ (colimit.isColimit _) }
#align category_theory.limits.has_limit_of_has_colimit_op CategoryTheory.Limits.hasLimit_of_hasColimit_op

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem hasLimitsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] :
    HasLimitsOfShape J Cᵒᵖ :=
  { HasLimit := fun F => hasLimit_of_hasColimit_leftOp F }
#align category_theory.limits.has_limits_of_shape_op_of_has_colimits_of_shape CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape

theorem hasLimitsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasLimitsOfShape J C :=
  { HasLimit := fun F => hasLimit_of_hasColimit_op F }
#align category_theory.limits.has_limits_of_shape_of_has_colimits_of_shape_op CategoryTheory.Limits.hasLimitsOfShape_of_hasColimitsOfShape_op

attribute [local instance] has_limits_of_shape_op_of_has_colimits_of_shape

/-- If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
instance hasLimits_op_of_hasColimits [HasColimits C] : HasLimits Cᵒᵖ :=
  ⟨inferInstance⟩
#align category_theory.limits.has_limits_op_of_has_colimits CategoryTheory.Limits.hasLimits_op_of_hasColimits

theorem hasLimits_of_hasColimits_op [HasColimits Cᵒᵖ] : HasLimits C :=
  { HasLimitsOfShape := fun J hJ => has_limits_of_shape_of_has_colimits_of_shape_op }
#align category_theory.limits.has_limits_of_has_colimits_op CategoryTheory.Limits.hasLimits_of_hasColimits_op

instance has_cofiltered_limits_op_of_has_filtered_colimits [HasFilteredColimitsOfSize.{v₂, u₂} C] :
    HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ
    where HasLimitsOfShape I hI₁ hI₂ := has_limits_of_shape_op_of_has_colimits_of_shape
#align category_theory.limits.has_cofiltered_limits_op_of_has_filtered_colimits CategoryTheory.Limits.has_cofiltered_limits_op_of_has_filtered_colimits

theorem has_cofiltered_limits_of_has_filtered_colimits_op [HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasCofilteredLimitsOfSize.{v₂, u₂} C :=
  { HasLimitsOfShape := fun I hI₂ hI₂ => has_limits_of_shape_of_has_colimits_of_shape_op }
#align category_theory.limits.has_cofiltered_limits_of_has_filtered_colimits_op CategoryTheory.Limits.has_cofiltered_limits_of_has_filtered_colimits_op

/-- If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
theorem hasColimit_of_hasLimit_leftOp (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F :=
  HasColimit.mk
    { Cocone := coconeOfConeLeftOp (limit.cone F.leftOp)
      IsColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }
#align category_theory.limits.has_colimit_of_has_limit_left_op CategoryTheory.Limits.hasColimit_of_hasLimit_leftOp

theorem hasColimit_of_hasLimit_op (F : J ⥤ C) [HasLimit F.op] : HasColimit F :=
  HasColimit.mk
    { Cocone := (limit.cone F.op).unop
      IsColimit := isColimitConeUnop _ (limit.isLimit _) }
#align category_theory.limits.has_colimit_of_has_limit_op CategoryTheory.Limits.hasColimit_of_hasLimit_op

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
instance hasColimitsOfShape_op_of_hasLimitsOfShape [HasLimitsOfShape Jᵒᵖ C] :
    HasColimitsOfShape J Cᵒᵖ where HasColimit F := hasColimit_of_hasLimit_leftOp F
#align category_theory.limits.has_colimits_of_shape_op_of_has_limits_of_shape CategoryTheory.Limits.hasColimitsOfShape_op_of_hasLimitsOfShape

theorem hasColimitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasColimitsOfShape J C :=
  { HasColimit := fun F => hasColimit_of_hasLimit_op F }
#align category_theory.limits.has_colimits_of_shape_of_has_limits_of_shape_op CategoryTheory.Limits.hasColimitsOfShape_of_hasLimitsOfShape_op

/-- If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
instance hasColimits_op_of_hasLimits [HasLimits C] : HasColimits Cᵒᵖ :=
  ⟨inferInstance⟩
#align category_theory.limits.has_colimits_op_of_has_limits CategoryTheory.Limits.hasColimits_op_of_hasLimits

theorem hasColimits_of_hasLimits_op [HasLimits Cᵒᵖ] : HasColimits C :=
  { HasColimitsOfShape := fun J hJ => has_colimits_of_shape_of_has_limits_of_shape_op }
#align category_theory.limits.has_colimits_of_has_limits_op CategoryTheory.Limits.hasColimits_of_hasLimits_op

instance has_filtered_colimits_op_of_has_cofiltered_limits [HasCofilteredLimitsOfSize.{v₂, u₂} C] :
    HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ where HasColimitsOfShape I hI₁ hI₂ := inferInstance
#align category_theory.limits.has_filtered_colimits_op_of_has_cofiltered_limits CategoryTheory.Limits.has_filtered_colimits_op_of_has_cofiltered_limits

theorem has_filtered_colimits_of_has_cofiltered_limits_op [HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasFilteredColimitsOfSize.{v₂, u₂} C :=
  { HasColimitsOfShape := fun I hI₁ hI₂ => has_colimits_of_shape_of_has_limits_of_shape_op }
#align category_theory.limits.has_filtered_colimits_of_has_cofiltered_limits_op CategoryTheory.Limits.has_filtered_colimits_of_has_cofiltered_limits_op

variable (X : Type v₂)

/-- If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
instance hasCoproductsOfShape_opposite [HasProductsOfShape X C] : HasCoproductsOfShape X Cᵒᵖ :=
  by
  haveI : has_limits_of_shape (discrete X)ᵒᵖ C :=
    has_limits_of_shape_of_equivalence (discrete.opposite X).symm
  infer_instance
#align category_theory.limits.has_coproducts_of_shape_opposite CategoryTheory.Limits.hasCoproductsOfShape_opposite

theorem hasCoproductsOfShape_of_opposite [HasProductsOfShape X Cᵒᵖ] : HasCoproductsOfShape X C :=
  haveI : has_limits_of_shape (discrete X)ᵒᵖ Cᵒᵖ :=
    has_limits_of_shape_of_equivalence (discrete.opposite X).symm
  has_colimits_of_shape_of_has_limits_of_shape_op
#align category_theory.limits.has_coproducts_of_shape_of_opposite CategoryTheory.Limits.hasCoproductsOfShape_of_opposite

/-- If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
instance hasProductsOfShape_opposite [HasCoproductsOfShape X C] : HasProductsOfShape X Cᵒᵖ :=
  by
  haveI : has_colimits_of_shape (discrete X)ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence (discrete.opposite X).symm
  infer_instance
#align category_theory.limits.has_products_of_shape_opposite CategoryTheory.Limits.hasProductsOfShape_opposite

theorem hasProductsOfShape_of_opposite [HasCoproductsOfShape X Cᵒᵖ] : HasProductsOfShape X C :=
  haveI : has_colimits_of_shape (discrete X)ᵒᵖ Cᵒᵖ :=
    has_colimits_of_shape_of_equivalence (discrete.opposite X).symm
  has_limits_of_shape_of_has_colimits_of_shape_op
#align category_theory.limits.has_products_of_shape_of_opposite CategoryTheory.Limits.hasProductsOfShape_of_opposite

instance hasProducts_opposite [HasCoproducts.{v₂} C] : HasProducts.{v₂} Cᵒᵖ := fun X =>
  inferInstance
#align category_theory.limits.has_products_opposite CategoryTheory.Limits.hasProducts_opposite

theorem hasProducts_of_opposite [HasCoproducts.{v₂} Cᵒᵖ] : HasProducts.{v₂} C := fun X =>
  hasProductsOfShape_of_opposite X
#align category_theory.limits.has_products_of_opposite CategoryTheory.Limits.hasProducts_of_opposite

instance hasCoproducts_opposite [HasProducts.{v₂} C] : HasCoproducts.{v₂} Cᵒᵖ := fun X =>
  inferInstance
#align category_theory.limits.has_coproducts_opposite CategoryTheory.Limits.hasCoproducts_opposite

theorem hasCoproducts_of_opposite [HasProducts.{v₂} Cᵒᵖ] : HasCoproducts.{v₂} C := fun X =>
  hasCoproductsOfShape_of_opposite X
#align category_theory.limits.has_coproducts_of_opposite CategoryTheory.Limits.hasCoproducts_of_opposite

instance hasFiniteCoproducts_opposite [HasFiniteProducts C] : HasFiniteCoproducts Cᵒᵖ
    where out n := Limits.hasCoproductsOfShape_opposite _
#align category_theory.limits.has_finite_coproducts_opposite CategoryTheory.Limits.hasFiniteCoproducts_opposite

theorem hasFiniteCoproducts_of_opposite [HasFiniteProducts Cᵒᵖ] : HasFiniteCoproducts C :=
  { out := fun n => hasCoproductsOfShape_of_opposite _ }
#align category_theory.limits.has_finite_coproducts_of_opposite CategoryTheory.Limits.hasFiniteCoproducts_of_opposite

instance hasFiniteProducts_opposite [HasFiniteCoproducts C] : HasFiniteProducts Cᵒᵖ
    where out n := inferInstance
#align category_theory.limits.has_finite_products_opposite CategoryTheory.Limits.hasFiniteProducts_opposite

theorem hasFiniteProducts_of_opposite [HasFiniteCoproducts Cᵒᵖ] : HasFiniteProducts C :=
  { out := fun n => hasProductsOfShape_of_opposite _ }
#align category_theory.limits.has_finite_products_of_opposite CategoryTheory.Limits.hasFiniteProducts_of_opposite

instance hasEqualizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ :=
  by
  haveI : has_colimits_of_shape walking_parallel_pairᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_parallel_pair_op_equiv
  infer_instance
#align category_theory.limits.has_equalizers_opposite CategoryTheory.Limits.hasEqualizers_opposite

instance hasCoequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ :=
  by
  haveI : has_limits_of_shape walking_parallel_pairᵒᵖ C :=
    has_limits_of_shape_of_equivalence walking_parallel_pair_op_equiv
  infer_instance
#align category_theory.limits.has_coequalizers_opposite CategoryTheory.Limits.hasCoequalizers_opposite

instance hasFiniteColimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ
    where out J 𝒟 𝒥 := by
    skip
    infer_instance
#align category_theory.limits.has_finite_colimits_opposite CategoryTheory.Limits.hasFiniteColimits_opposite

instance hasFiniteLimits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ
    where out J 𝒟 𝒥 := by
    skip
    infer_instance
#align category_theory.limits.has_finite_limits_opposite CategoryTheory.Limits.hasFiniteLimits_opposite

instance hasPullbacks_opposite [HasPushouts C] : HasPullbacks Cᵒᵖ :=
  by
  haveI : has_colimits_of_shape walking_cospanᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_cospan_op_equiv.symm
  apply has_limits_of_shape_op_of_has_colimits_of_shape
#align category_theory.limits.has_pullbacks_opposite CategoryTheory.Limits.hasPullbacks_opposite

instance hasPushouts_opposite [HasPullbacks C] : HasPushouts Cᵒᵖ :=
  by
  haveI : has_limits_of_shape walking_spanᵒᵖ C :=
    has_limits_of_shape_of_equivalence walking_span_op_equiv.symm
  infer_instance
#align category_theory.limits.has_pushouts_opposite CategoryTheory.Limits.hasPushouts_opposite

/-- The canonical isomorphism relating `span f.op g.op` and `(cospan f g).op` -/
@[simps]
def spanOp {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.op g.op ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
  NatIso.ofComponents (by rintro (_ | _ | _) <;> rfl)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> tidy)
#align category_theory.limits.span_op CategoryTheory.Limits.spanOp

/-- The canonical isomorphism relating `(cospan f g).op` and `span f.op g.op` -/
@[simps]
def opCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).op ≅ walkingCospanOpEquiv.Functor ⋙ span f.op g.op :=
  calc
    (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op := by rfl
    _ ≅ (walkingCospanOpEquiv.Functor ⋙ walkingCospanOpEquiv.inverse) ⋙ (cospan f g).op :=
      (isoWhiskerRight walkingCospanOpEquiv.unitIso _)
    _ ≅ walkingCospanOpEquiv.Functor ⋙ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
      (Functor.associator _ _ _)
    _ ≅ walkingCospanOpEquiv.Functor ⋙ span f.op g.op := isoWhiskerLeft _ (spanOp f g).symm
    
#align category_theory.limits.op_cospan CategoryTheory.Limits.opCospan

/-- The canonical isomorphism relating `cospan f.op g.op` and `(span f g).op` -/
@[simps]
def cospanOp {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.op g.op ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
  NatIso.ofComponents (by rintro (_ | _ | _) <;> rfl)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> tidy)
#align category_theory.limits.cospan_op CategoryTheory.Limits.cospanOp

/-- The canonical isomorphism relating `(span f g).op` and `cospan f.op g.op` -/
@[simps]
def opSpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    (span f g).op ≅ walkingSpanOpEquiv.Functor ⋙ cospan f.op g.op :=
  calc
    (span f g).op ≅ 𝟭 _ ⋙ (span f g).op := by rfl
    _ ≅ (walkingSpanOpEquiv.Functor ⋙ walkingSpanOpEquiv.inverse) ⋙ (span f g).op :=
      (isoWhiskerRight walkingSpanOpEquiv.unitIso _)
    _ ≅ walkingSpanOpEquiv.Functor ⋙ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
      (Functor.associator _ _ _)
    _ ≅ walkingSpanOpEquiv.Functor ⋙ cospan f.op g.op := isoWhiskerLeft _ (cospanOp f g).symm
    
#align category_theory.limits.op_span CategoryTheory.Limits.opSpan

namespace PushoutCocone

/-- The obvious map `pushout_cocone f g → pullback_cone f.unop g.unop` -/
@[simps (config := lemmasOnly)]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    PullbackCone f.unop g.unop :=
  Cocone.unop
    ((Cocones.precompose (opCospan f.unop g.unop).hom).obj
      (Cocone.whisker walkingCospanOpEquiv.Functor c))
#align category_theory.limits.pushout_cocone.unop CategoryTheory.Limits.PushoutCocone.unop

@[simp]
theorem unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.fst = c.inl.unop :=
  by
  change (_ : limits.cone _).π.app _ = _
  simp only [pushout_cocone.ι_app_left, pushout_cocone.unop_π_app]
  tidy
#align category_theory.limits.pushout_cocone.unop_fst CategoryTheory.Limits.PushoutCocone.unop_fst

@[simp]
theorem unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.snd = c.inr.unop :=
  by
  change (_ : limits.cone _).π.app _ = _
  simp only [pushout_cocone.unop_π_app, pushout_cocone.ι_app_right]
  tidy
#align category_theory.limits.pushout_cocone.unop_snd CategoryTheory.Limits.PushoutCocone.unop_snd

/-- The obvious map `pushout_cocone f.op g.op → pullback_cone f g` -/
@[simps (config := lemmasOnly)]
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackCone f.op g.op :=
  (Cones.postcompose (cospanOp f g).symm.hom).obj
    (Cone.whisker walkingSpanOpEquiv.inverse (Cocone.op c))
#align category_theory.limits.pushout_cocone.op CategoryTheory.Limits.PushoutCocone.op

@[simp]
theorem op_fst {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.fst = c.inl.op :=
  by
  change (_ : limits.cone _).π.app _ = _
  apply category.comp_id
#align category_theory.limits.pushout_cocone.op_fst CategoryTheory.Limits.PushoutCocone.op_fst

@[simp]
theorem op_snd {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.snd = c.inr.op :=
  by
  change (_ : limits.cone _).π.app _ = _
  apply category.comp_id
#align category_theory.limits.pushout_cocone.op_snd CategoryTheory.Limits.PushoutCocone.op_snd

end PushoutCocone

namespace PullbackCone

/-- The obvious map `pullback_cone f g → pushout_cocone f.unop g.unop` -/
@[simps (config := lemmasOnly)]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    PushoutCocone f.unop g.unop :=
  Cone.unop
    ((Cones.postcompose (opSpan f.unop g.unop).symm.hom).obj
      (Cone.whisker walkingSpanOpEquiv.Functor c))
#align category_theory.limits.pullback_cone.unop CategoryTheory.Limits.PullbackCone.unop

@[simp]
theorem unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inl = c.fst.unop :=
  by
  change (_ : limits.cocone _).ι.app _ = _
  dsimp only [unop, op_span]
  simp; dsimp; simp; dsimp; simp
#align category_theory.limits.pullback_cone.unop_inl CategoryTheory.Limits.PullbackCone.unop_inl

@[simp]
theorem unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inr = c.snd.unop :=
  by
  change (_ : limits.cocone _).ι.app _ = _
  apply Quiver.Hom.op_inj
  simp [unop_ι_app]; dsimp; simp
  apply category.comp_id
#align category_theory.limits.pullback_cone.unop_inr CategoryTheory.Limits.PullbackCone.unop_inr

/-- The obvious map `pullback_cone f g → pushout_cocone f.op g.op` -/
@[simps (config := lemmasOnly)]
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCocone f.op g.op :=
  (Cocones.precompose (spanOp f g).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.inverse (Cone.op c))
#align category_theory.limits.pullback_cone.op CategoryTheory.Limits.PullbackCone.op

@[simp]
theorem op_inl {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.inl = c.fst.op :=
  by
  change (_ : limits.cocone _).ι.app _ = _
  apply category.id_comp
#align category_theory.limits.pullback_cone.op_inl CategoryTheory.Limits.PullbackCone.op_inl

@[simp]
theorem op_inr {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.inr = c.snd.op :=
  by
  change (_ : limits.cocone _).ι.app _ = _
  apply category.id_comp
#align category_theory.limits.pullback_cone.op_inr CategoryTheory.Limits.PullbackCone.op_inr

/-- If `c` is a pullback cone, then `c.op.unop` is isomorphic to `c`. -/
def opUnop {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.unop ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)
#align category_theory.limits.pullback_cone.op_unop CategoryTheory.Limits.PullbackCone.opUnop

/-- If `c` is a pullback cone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOp {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.unop.op ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)
#align category_theory.limits.pullback_cone.unop_op CategoryTheory.Limits.PullbackCone.unopOp

end PullbackCone

namespace PushoutCocone

/-- If `c` is a pushout cocone, then `c.op.unop` is isomorphic to `c`. -/
def opUnop {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.unop ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)
#align category_theory.limits.pushout_cocone.op_unop CategoryTheory.Limits.PushoutCocone.opUnop

/-- If `c` is a pushout cocone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.unop.op ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)
#align category_theory.limits.pushout_cocone.unop_op CategoryTheory.Limits.PushoutCocone.unopOp

/-- A pushout cone is a colimit cocone if and only if the corresponding pullback cone
in the opposite category is a limit cone. -/
def isColimitEquivIsLimitOp {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.op :=
  by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    equiv_rw is_limit.postcompose_hom_equiv _ _
    equiv_rw(is_limit.whisker_equivalence_equiv walking_span_op_equiv.symm).symm
    exact is_limit_cocone_op _ h
  · intro h
    equiv_rw is_colimit.equiv_iso_colimit c.op_unop.symm
    apply is_colimit_cone_unop
    equiv_rw is_limit.postcompose_hom_equiv _ _
    equiv_rw(is_limit.whisker_equivalence_equiv _).symm
    exact h
#align category_theory.limits.pushout_cocone.is_colimit_equiv_is_limit_op CategoryTheory.Limits.PushoutCocone.isColimitEquivIsLimitOp

/-- A pushout cone is a colimit cocone in `Cᵒᵖ` if and only if the corresponding pullback cone
in `C` is a limit cone. -/
def isColimitEquivIsLimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.unop :=
  by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    apply is_limit_cocone_unop
    equiv_rw is_colimit.precompose_hom_equiv _ _
    equiv_rw(is_colimit.whisker_equivalence_equiv _).symm
    exact h
  · intro h
    equiv_rw is_colimit.equiv_iso_colimit c.unop_op.symm
    equiv_rw is_colimit.precompose_hom_equiv _ _
    equiv_rw(is_colimit.whisker_equivalence_equiv walking_cospan_op_equiv.symm).symm
    exact is_colimit_cone_op _ h
#align category_theory.limits.pushout_cocone.is_colimit_equiv_is_limit_unop CategoryTheory.Limits.PushoutCocone.isColimitEquivIsLimitUnop

end PushoutCocone

namespace PullbackCone

/-- A pullback cone is a limit cone if and only if the corresponding pushout cocone
in the opposite category is a colimit cocone. -/
def isLimitEquivIsColimitOp {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.op_unop).symm.trans c.op.isColimitEquivIsLimitUnop.symm
#align category_theory.limits.pullback_cone.is_limit_equiv_is_colimit_op CategoryTheory.Limits.PullbackCone.isLimitEquivIsColimitOp

/-- A pullback cone is a limit cone in `Cᵒᵖ` if and only if the corresponding pushout cocone
in `C` is a colimit cocone. -/
def isLimitEquivIsColimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unop_op).symm.trans c.unop.isColimitEquivIsLimitOp.symm
#align category_theory.limits.pullback_cone.is_limit_equiv_is_colimit_unop CategoryTheory.Limits.PullbackCone.isLimitEquivIsColimitUnop

end PullbackCone

section Pullback

open Opposite

/-- The pullback of `f` and `g` in `C` is isomorphic to the pushout of
`f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable def pullbackIsoUnopPushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] : pullback f g ≅ unop (pushout f.op g.op) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    ((PushoutCocone.isColimitEquivIsLimitUnop _) (colimit.isColimit (span f.op g.op)))
#align category_theory.limits.pullback_iso_unop_pushout CategoryTheory.Limits.pullbackIsoUnopPushout

@[simp, reassoc.1]
theorem pullbackIsoUnopPushout_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.fst = (pushout.inl : _ ⟶ pushout f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)
#align category_theory.limits.pullback_iso_unop_pushout_inv_fst CategoryTheory.Limits.pullbackIsoUnopPushout_inv_fst

@[simp, reassoc.1]
theorem pullbackIsoUnopPushout_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.snd = (pushout.inr : _ ⟶ pushout f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)
#align category_theory.limits.pullback_iso_unop_pushout_inv_snd CategoryTheory.Limits.pullbackIsoUnopPushout_inv_snd

@[simp, reassoc.1]
theorem pullbackIsoUnopPushout_hom_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] : pushout.inl ≫ (pullbackIsoUnopPushout f g).hom.op = pullback.fst.op :=
  by
  apply Quiver.Hom.unop_inj
  dsimp
  rw [← pullback_iso_unop_pushout_inv_fst, iso.hom_inv_id_assoc]
#align category_theory.limits.pullback_iso_unop_pushout_hom_inl CategoryTheory.Limits.pullbackIsoUnopPushout_hom_inl

@[simp, reassoc.1]
theorem pullbackIsoUnopPushout_hom_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPushout f.op g.op] : pushout.inr ≫ (pullbackIsoUnopPushout f g).hom.op = pullback.snd.op :=
  by
  apply Quiver.Hom.unop_inj
  dsimp
  rw [← pullback_iso_unop_pushout_inv_snd, iso.hom_inv_id_assoc]
#align category_theory.limits.pullback_iso_unop_pushout_hom_inr CategoryTheory.Limits.pullbackIsoUnopPushout_hom_inr

end Pullback

section Pushout

/-- The pushout of `f` and `g` in `C` is isomorphic to the pullback of
 `f.op` and `g.op` in `Cᵒᵖ`. -/
noncomputable def pushoutIsoUnopPullback {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] : pushout f g ≅ unop (pullback f.op g.op) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    ((PullbackCone.isLimitEquivIsColimitUnop _) (limit.isLimit (cospan f.op g.op)))
#align category_theory.limits.pushout_iso_unop_pullback CategoryTheory.Limits.pushoutIsoUnopPullback

@[simp, reassoc.1]
theorem pushoutIsoUnopPullback_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    pushout.inl ≫ (pushoutIsoUnopPullback f g).hom = (pullback.fst : pullback f.op g.op ⟶ _).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)
#align category_theory.limits.pushout_iso_unop_pullback_inl_hom CategoryTheory.Limits.pushoutIsoUnopPullback_inl_hom

@[simp, reassoc.1]
theorem pushoutIsoUnopPullback_inr_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] :
    pushout.inr ≫ (pushoutIsoUnopPullback f g).hom = (pullback.snd : pullback f.op g.op ⟶ _).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)
#align category_theory.limits.pushout_iso_unop_pullback_inr_hom CategoryTheory.Limits.pushoutIsoUnopPullback_inr_hom

@[simp]
theorem pushoutIsoUnopPullback_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] : (pushoutIsoUnopPullback f g).inv.op ≫ pullback.fst = pushout.inl.op :=
  by
  apply Quiver.Hom.unop_inj
  dsimp
  rw [← pushout_iso_unop_pullback_inl_hom, category.assoc, iso.hom_inv_id, category.comp_id]
#align category_theory.limits.pushout_iso_unop_pullback_inv_fst CategoryTheory.Limits.pushoutIsoUnopPullback_inv_fst

@[simp]
theorem pushoutIsoUnopPullback_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g]
    [HasPullback f.op g.op] : (pushoutIsoUnopPullback f g).inv.op ≫ pullback.snd = pushout.inr.op :=
  by
  apply Quiver.Hom.unop_inj
  dsimp
  rw [← pushout_iso_unop_pullback_inr_hom, category.assoc, iso.hom_inv_id, category.comp_id]
#align category_theory.limits.pushout_iso_unop_pullback_inv_snd CategoryTheory.Limits.pushoutIsoUnopPullback_inv_snd

end Pushout

end CategoryTheory.Limits

