/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We construct limits and colimits in the opposite categories.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

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

/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`. -/
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
def isColimitCoconeOfConeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsLimit c) :
    IsColimit (coconeOfConeUnop c) where
  desc s := (hc.lift (coneUnopOfCocone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using w (op j)

/-- Turn a limit for `F.leftOp : Jᵒᵖ ⥤ C` into a colimit for `F : J ⥤ Cᵒᵖ`. -/
@[simps!]
def isColimitOfConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F}
    (hc : IsLimit (coneLeftOpOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeLeftOp F hc

/-- Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps!]
def isLimitOfCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F}
    (hc : IsColimit (coconeLeftOpOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeLeftOp F hc

/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`. -/
@[simps!]
def isColimitOfConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F}
    (hc : IsLimit (coneRightOpOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeRightOp F hc

/-- Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps!]
def isLimitOfCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F}
    (hc : IsColimit (coconeRightOpOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeRightOp F hc

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps!]
def isColimitOfConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F}
    (hc : IsLimit (coneUnopOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeUnop F hc

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps!]
def isLimitOfCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F}
    (hc : IsColimit (coconeUnopOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeUnop F hc

/-- Turn a limit for `F : J ⥤ Cᵒᵖ` into a colimit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps!]
def isColimitOfConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp}
    (hc : IsLimit (coneOfCoconeLeftOp c)) : IsColimit c :=
  isColimitCoconeLeftOpOfCone F hc

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps!]
def isLimitOfCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp}
    (hc : IsColimit (coconeOfConeLeftOp c)) : IsLimit c :=
  isLimitConeLeftOpOfCocone F hc

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ.` -/
@[simps!]
def isColimitOfConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp}
    (hc : IsLimit (coneOfCoconeRightOp c)) : IsColimit c :=
  isColimitCoconeRightOpOfCone F hc

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps!]
def isLimitOfCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp}
    (hc : IsColimit (coconeOfConeRightOp c)) : IsLimit c :=
  isLimitConeRightOpOfCocone F hc

/-- Turn a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F.unop : J ⥤ C`. -/
@[simps!]
def isColimitOfConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop}
    (hc : IsLimit (coneOfCoconeUnop c)) : IsColimit c :=
  isColimitCoconeUnopOfCone F hc

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps!]
def isLimitOfCoconeOfConeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop}
    (hc : IsColimit (coconeOfConeUnop c)) : IsLimit c :=
  isLimitConeUnopOfCocone F hc

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

theorem hasLimit_of_hasColimit_rightOp (F : Jᵒᵖ ⥤ C) [HasColimit F.rightOp] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeRightOp (colimit.cocone F.rightOp)
      isLimit := isLimitConeOfCoconeRightOp _ (colimit.isColimit _) }

theorem hasLimit_of_hasColimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F.unop] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeUnop (colimit.cocone F.unop)
      isLimit := isLimitConeOfCoconeUnop _ (colimit.isColimit _) }

instance hasLimit_op_of_hasColimit (F : J ⥤ C) [HasColimit F] : HasLimit F.op :=
  HasLimit.mk
    { cone := (colimit.cocone F).op
      isLimit := (colimit.isColimit _).op }

instance hasLimit_leftOp_of_hasColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.leftOp :=
  HasLimit.mk
    { cone := coneLeftOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeLeftOpOfCocone _ (colimit.isColimit _) }

instance hasLimit_rightOp_of_hasColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] : HasLimit F.rightOp :=
  HasLimit.mk
    { cone := coneRightOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeRightOpOfCocone _ (colimit.isColimit _) }

instance hasLimit_unop_of_hasColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.unop :=
  HasLimit.mk
    { cone := coneUnopOfCocone (colimit.cocone F)
      isLimit := isLimitConeUnopOfCocone _ (colimit.isColimit _) }

/-- The limit of `F.op` is the opposite of `colimit F`. -/
def limitOpIsoOpColimit (F : J ⥤ C) [HasColimit F] :
    limit F.op ≅ op (colimit F) :=
  limit.isoLimitCone ⟨_, (colimit.isColimit _).op⟩

@[reassoc (attr := simp)]
lemma limitOpIsoOpColimit_inv_comp_π (F : J ⥤ C) [HasColimit F] (j : Jᵒᵖ) :
    (limitOpIsoOpColimit F).inv ≫ limit.π F.op j = (colimit.ι F j.unop).op := by
  simp [limitOpIsoOpColimit]

@[reassoc (attr := simp)]
lemma limitOpIsoOpColimit_hom_comp_ι (F : J ⥤ C) [HasColimit F] (j : J) :
    (limitOpIsoOpColimit F).hom ≫ (colimit.ι F j).op = limit.π F.op (op j) := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.leftOp` is the unopposite of `colimit F`. -/
def limitLeftOpIsoUnopColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] :
    limit F.leftOp ≅ unop (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeLeftOpOfCocone _ (colimit.isColimit _)⟩

@[reassoc (attr := simp)]
lemma limitLeftOpIsoUnopColimit_inv_comp_π (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ) :
    (limitLeftOpIsoUnopColimit F).inv ≫ limit.π F.leftOp j = (colimit.ι F j.unop).unop := by
  simp [limitLeftOpIsoUnopColimit]

@[reassoc (attr := simp)]
lemma limitLeftOpIsoUnopColimit_hom_comp_ι (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : J) :
    (limitLeftOpIsoUnopColimit F).hom ≫ (colimit.ι F j).unop = limit.π F.leftOp (op j) := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.rightOp` is the opposite of `colimit F`. -/
def limitRightOpIsoOpColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] :
    limit F.rightOp ≅ op (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeRightOpOfCocone _ (colimit.isColimit _)⟩

@[reassoc (attr := simp)]
lemma limitRightOpIsoOpColimit_inv_comp_π (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : J) :
    (limitRightOpIsoOpColimit F).inv ≫ limit.π F.rightOp j = (colimit.ι F (op j)).op := by
  simp [limitRightOpIsoOpColimit]

@[reassoc (attr := simp)]
lemma limitRightOpIsoOpColimit_hom_comp_ι (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : Jᵒᵖ) :
    (limitRightOpIsoOpColimit F).hom ≫ (colimit.ι F j).op = limit.π F.rightOp j.unop := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.unop` is the unopposite of `colimit F`. -/
def limitUnopIsoUnopColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] :
    limit F.unop ≅ unop (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeUnopOfCocone _ (colimit.isColimit _)⟩

@[reassoc (attr := simp)]
lemma limitUnopIsoUnopColimit_inv_comp_π (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : J) :
    (limitUnopIsoUnopColimit F).inv ≫ limit.π F.unop j = (colimit.ι F (op j)).unop := by
  simp [limitUnopIsoUnopColimit]

@[reassoc (attr := simp)]
lemma limitUnopIsoUnopColimit_hom_comp_ι (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ) :
    (limitUnopIsoUnopColimit F).hom ≫ (colimit.ι F j).unop = limit.π F.unop j.unop := by
  simp [← Iso.eq_inv_comp]

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
instance hasLimits_op_of_hasColimits [HasColimitsOfSize.{v₂, u₂} C] :
    HasLimitsOfSize.{v₂, u₂} Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩

theorem hasLimits_of_hasColimits_op [HasColimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasLimitsOfSize.{v₂, u₂} C :=
  { has_limits_of_shape := fun _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

/-- If `F.leftOp : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`. -/
theorem hasColimit_of_hasLimit_leftOp (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeLeftOp (limit.cone F.leftOp)
      isColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }

theorem hasColimit_of_hasLimit_op (F : J ⥤ C) [HasLimit F.op] : HasColimit F :=
  HasColimit.mk
    { cocone := (limit.cone F.op).unop
      isColimit := (limit.isLimit _).unop }

theorem hasColimit_of_hasLimit_rightOp (F : Jᵒᵖ ⥤ C) [HasLimit F.rightOp] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeRightOp (limit.cone F.rightOp)
      isColimit := isColimitCoconeOfConeRightOp _ (limit.isLimit _) }

theorem hasColimit_of_hasLimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F.unop] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeUnop (limit.cone F.unop)
      isColimit := isColimitCoconeOfConeUnop _ (limit.isLimit _) }

instance hasColimit_op_of_hasLimit (F : J ⥤ C) [HasLimit F] : HasColimit F.op :=
  HasColimit.mk
    { cocone := (limit.cone F).op
      isColimit := (limit.isLimit _).op }

instance hasColimit_leftOp_of_hasLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] : HasColimit F.leftOp :=
  HasColimit.mk
    { cocone := coconeLeftOpOfCone (limit.cone F)
      isColimit := isColimitCoconeLeftOpOfCone _ (limit.isLimit _) }

instance hasColimit_rightOp_of_hasLimit (F : Jᵒᵖ ⥤ C) [HasLimit F] : HasColimit F.rightOp :=
  HasColimit.mk
    { cocone := coconeRightOpOfCone (limit.cone F)
      isColimit := isColimitCoconeRightOpOfCone _ (limit.isLimit _) }

instance hasColimit_unop_of_hasLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] : HasColimit F.unop :=
  HasColimit.mk
    { cocone := coconeUnopOfCone (limit.cone F)
      isColimit := isColimitCoconeUnopOfCone _ (limit.isLimit _) }

/-- The colimit of `F.op` is the opposite of `limit F`. -/
def colimitOpIsoOpLimit (F : J ⥤ C) [HasLimit F] :
    colimit F.op ≅ op (limit F) :=
  colimit.isoColimitCocone ⟨_, (limit.isLimit _).op⟩

@[reassoc (attr := simp)]
lemma ι_comp_colimitOpIsoOpLimit_hom (F : J ⥤ C) [HasLimit F] (j : Jᵒᵖ) :
    colimit.ι F.op j ≫ (colimitOpIsoOpLimit F).hom = (limit.π F j.unop).op := by
  simp [colimitOpIsoOpLimit]

@[reassoc (attr := simp)]
lemma π_comp_colimitOpIsoOpLimit_inv (F : J ⥤ C) [HasLimit F] (j : J) :
    (limit.π F j).op ≫ (colimitOpIsoOpLimit F).inv = colimit.ι F.op (op j) := by
  simp [Iso.comp_inv_eq]

/-- The colimit of `F.leftOp` is the unopposite of `limit F`. -/
def colimitLeftOpIsoUnopLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] :
    colimit F.leftOp ≅ unop (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeLeftOpOfCone _ (limit.isLimit _)⟩

@[reassoc (attr := simp)]
lemma ι_comp_colimitLeftOpIsoUnopLimit_hom (F : J ⥤ Cᵒᵖ) [HasLimit F] (j : Jᵒᵖ) :
    colimit.ι F.leftOp j ≫ (colimitLeftOpIsoUnopLimit F).hom = (limit.π F j.unop).unop := by
  simp [colimitLeftOpIsoUnopLimit]

@[reassoc (attr := simp)]
lemma π_comp_colimitLeftOpIsoUnopLimit_inv (F : J ⥤ Cᵒᵖ) [HasLimit F] (j : J) :
    (limit.π F j).unop ≫ (colimitLeftOpIsoUnopLimit F).inv = colimit.ι F.leftOp (op j) := by
  simp [Iso.comp_inv_eq]

/-- The colimit of `F.rightOp` is the opposite of `limit F`. -/
def colimitRightOpIsoUnopLimit (F : Jᵒᵖ ⥤ C) [HasLimit F] :
    colimit F.rightOp ≅ op (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeRightOpOfCone _ (limit.isLimit _)⟩

@[reassoc (attr := simp)]
lemma ι_comp_colimitRightOpIsoUnopLimit_hom (F : Jᵒᵖ ⥤ C) [HasLimit F] (j : J) :
    colimit.ι F.rightOp j ≫ (colimitRightOpIsoUnopLimit F).hom = (limit.π F (op j)).op := by
  simp [colimitRightOpIsoUnopLimit]

@[reassoc (attr := simp)]
lemma π_comp_colimitRightOpIsoUnopLimit_inv (F : Jᵒᵖ ⥤ C) [HasLimit F] (j : Jᵒᵖ) :
    (limit.π F j).op ≫ (colimitRightOpIsoUnopLimit F).inv = colimit.ι F.rightOp j.unop := by
  simp [Iso.comp_inv_eq]

/-- The colimit of `F.unop` is the unopposite of `limit F`. -/
def colimitUnopIsoOpLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] :
    colimit F.unop ≅ unop (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeUnopOfCone _ (limit.isLimit _)⟩

@[reassoc (attr := simp)]
lemma ι_comp_colimitUnopIsoOpLimit_hom (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] (j : J) :
    colimit.ι F.unop j ≫ (colimitUnopIsoOpLimit F).hom = (limit.π F (op j)).unop := by
  simp [colimitUnopIsoOpLimit]

@[reassoc (attr := simp)]
lemma π_comp_colimitUnopIsoOpLimit_inv (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] (j : Jᵒᵖ) :
    (limit.π F j).unop ≫ (colimitUnopIsoOpLimit F).inv = colimit.ι F.unop j.unop := by
  simp [Iso.comp_inv_eq]

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
instance hasColimitsOfShape_op_of_hasLimitsOfShape [HasLimitsOfShape Jᵒᵖ C] :
    HasColimitsOfShape J Cᵒᵖ where has_colimit F := hasColimit_of_hasLimit_leftOp F

theorem hasColimitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasColimitsOfShape J C :=
  { has_colimit := fun F => hasColimit_of_hasLimit_op F }

/-- If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
instance hasColimits_op_of_hasLimits [HasLimitsOfSize.{v₂, u₂} C] :
    HasColimitsOfSize.{v₂, u₂} Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩

theorem hasColimits_of_hasLimits_op [HasLimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasColimitsOfSize.{v₂, u₂} C :=
  { has_colimits_of_shape := fun _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

instance hasFiniteColimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ :=
  ⟨fun _ _ _ => hasColimitsOfShape_op_of_hasLimitsOfShape⟩

instance hasFiniteLimits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ :=
  ⟨fun _ _ _ => hasLimitsOfShape_op_of_hasColimitsOfShape⟩

end CategoryTheory.Limits
