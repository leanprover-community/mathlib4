/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We construct limits and colimits in the opposite categories.
-/

@[expose] public section


universe w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps)
/-- Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.leftOp : Jᵒᵖ ⥤ C`. -/]
def isLimitConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneLeftOpOfCocone c) where
  lift s := (hc.desc (coconeOfConeLeftOp s)).unop
  fac s j :=
    Quiver.Hom.op_inj <| by
      simp only [coneLeftOpOfCocone_π_app, op_comp, Quiver.Hom.op_unop, IsColimit.fac,
        coconeOfConeLeftOp_ι_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac, coconeOfConeLeftOp_ι_app] using! w (op j)

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps)
/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ`. -/]
def isLimitConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneRightOpOfCocone c) where
  lift s := (hc.desc (coconeOfConeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using! w (unop j)

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[to_dual (attr := simps)
/-- Turn a limit of `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit of `F.unop : J ⥤ C`. -/]
def isLimitConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneUnopOfCocone c) where
  lift s := (hc.desc (coconeOfConeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using! w (unop j)

/-- Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps)
/-- Turn a limit of `F.leftOp : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`. -/]
def isLimitConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeLeftOp c) where
  lift s := (hc.desc (coconeLeftOpOfCone s)).op
  fac s j :=
    Quiver.Hom.unop_inj <| by
      simp only [coneOfCoconeLeftOp_π_app, unop_comp, Quiver.Hom.unop_op, IsColimit.fac,
        coconeLeftOpOfCone_ι_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac, coneOfCoconeLeftOp_π_app] using! w (unop j)

/-- Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps)
/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`. -/]
def isLimitConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeRightOp c) where
  lift s := (hc.desc (coconeRightOpOfCone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using! w (op j)

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps)
/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/]
def isLimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsColimit c) :
    IsLimit (coneOfCoconeUnop c) where
  lift s := (hc.desc (coconeUnopOfCone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using! w (op j)

/-- Turn a limit for `F.leftOp : Jᵒᵖ ⥤ C` into a colimit for `F : J ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps!)
/-- Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/]
def isColimitOfConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F}
    (hc : IsLimit (coneLeftOpOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeLeftOp F hc

/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps!)
/-- Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/]
def isColimitOfConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F}
    (hc : IsLimit (coneRightOpOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeRightOp F hc

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps!)
/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/]
def isColimitOfConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F}
    (hc : IsLimit (coneUnopOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeUnop F hc

/-- Turn a limit for `F : J ⥤ Cᵒᵖ` into a colimit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps!)
/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`. -/]
def isColimitOfConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp}
    (hc : IsLimit (coneOfCoconeLeftOp c)) : IsColimit c :=
  isColimitCoconeLeftOpOfCone F hc

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ.` -/
@[to_dual (attr := simps!)
/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`. -/]
def isColimitOfConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp}
    (hc : IsLimit (coneOfCoconeRightOp c)) : IsColimit c :=
  isColimitCoconeRightOpOfCone F hc

/-- Turn a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F.unop : J ⥤ C`. -/
@[to_dual (attr := simps!)
/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/]
def isColimitOfConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop}
    (hc : IsLimit (coneOfCoconeUnop c)) : IsColimit c :=
  isColimitCoconeUnopOfCone F hc

/-- If `F.leftOp : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
@[to_dual
/-- If `F.leftOp : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`. -/]
theorem hasLimit_of_hasColimit_leftOp (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeLeftOp (colimit.cocone F.leftOp)
      isLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }

@[to_dual]
theorem hasLimit_of_hasColimit_op (F : J ⥤ C) [HasColimit F.op] : HasLimit F :=
  HasLimit.mk
    { cone := (colimit.cocone F.op).unop
      isLimit := (colimit.isColimit _).unop }

@[to_dual]
theorem hasLimit_of_hasColimit_rightOp (F : Jᵒᵖ ⥤ C) [HasColimit F.rightOp] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeRightOp (colimit.cocone F.rightOp)
      isLimit := isLimitConeOfCoconeRightOp _ (colimit.isColimit _) }

@[to_dual]
theorem hasLimit_of_hasColimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F.unop] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeUnop (colimit.cocone F.unop)
      isLimit := isLimitConeOfCoconeUnop _ (colimit.isColimit _) }

@[to_dual]
instance hasLimit_op_of_hasColimit (F : J ⥤ C) [HasColimit F] : HasLimit F.op :=
  HasLimit.mk
    { cone := (colimit.cocone F).op
      isLimit := (colimit.isColimit _).op }

@[to_dual]
instance hasLimit_leftOp_of_hasColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.leftOp :=
  HasLimit.mk
    { cone := coneLeftOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeLeftOpOfCocone _ (colimit.isColimit _) }

@[to_dual]
instance hasLimit_rightOp_of_hasColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] : HasLimit F.rightOp :=
  HasLimit.mk
    { cone := coneRightOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeRightOpOfCocone _ (colimit.isColimit _) }

@[to_dual]
instance hasLimit_unop_of_hasColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.unop :=
  HasLimit.mk
    { cone := coneUnopOfCocone (colimit.cocone F)
      isLimit := isLimitConeUnopOfCocone _ (colimit.isColimit _) }

/-- The limit of `F.op` is the opposite of `colimit F`. -/
@[to_dual /-- The colimit of `F.op` is the opposite of `limit F`. -/]
def limitOpIsoOpColimit (F : J ⥤ C) [HasColimit F] :
    limit F.op ≅ op (colimit F) :=
  limit.isoLimitCone ⟨_, (colimit.isColimit _).op⟩

@[to_dual (attr := reassoc (attr := simp)) ι_comp_colimitOpIsoOpLimit_hom]
lemma limitOpIsoOpColimit_inv_comp_π (F : J ⥤ C) [HasColimit F] (j : Jᵒᵖ) :
    (limitOpIsoOpColimit F).inv ≫ limit.π F.op j = (colimit.ι F j.unop).op := by
  simp [limitOpIsoOpColimit]

@[to_dual (attr := reassoc (attr := simp)) π_comp_colimitOpIsoOpLimit_inv]
lemma limitOpIsoOpColimit_hom_comp_ι (F : J ⥤ C) [HasColimit F] (j : J) :
    (limitOpIsoOpColimit F).hom ≫ (colimit.ι F j).op = limit.π F.op (op j) := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.leftOp` is the unopposite of `colimit F`. -/
@[to_dual /-- The colimit of `F.leftOp` is the unopposite of `limit F`. -/]
def limitLeftOpIsoUnopColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] :
    limit F.leftOp ≅ unop (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeLeftOpOfCocone _ (colimit.isColimit _)⟩

@[to_dual (attr := reassoc (attr := simp)) ι_comp_colimitLeftOpIsoUnopLimit_hom]
lemma limitLeftOpIsoUnopColimit_inv_comp_π (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ) :
    (limitLeftOpIsoUnopColimit F).inv ≫ limit.π F.leftOp j = (colimit.ι F j.unop).unop := by
  simp [limitLeftOpIsoUnopColimit]

@[to_dual (attr := reassoc (attr := simp)) π_comp_colimitLeftOpIsoUnopLimit_inv]
lemma limitLeftOpIsoUnopColimit_hom_comp_ι (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : J) :
    (limitLeftOpIsoUnopColimit F).hom ≫ (colimit.ι F j).unop = limit.π F.leftOp (op j) := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.rightOp` is the opposite of `colimit F`. -/
@[to_dual /-- The colimit of `F.rightOp` is the opposite of `limit F`. -/]
def limitRightOpIsoOpColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] :
    limit F.rightOp ≅ op (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeRightOpOfCocone _ (colimit.isColimit _)⟩

@[to_dual (attr := reassoc (attr := simp)) ι_comp_colimitRightOpIsoOpLimit_hom]
lemma limitRightOpIsoOpColimit_inv_comp_π (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : J) :
    (limitRightOpIsoOpColimit F).inv ≫ limit.π F.rightOp j = (colimit.ι F (op j)).op := by
  simp [limitRightOpIsoOpColimit]

@[to_dual (attr := reassoc (attr := simp)) π_comp_colimitRightOpIsoOpLimit_inv]
lemma limitRightOpIsoOpColimit_hom_comp_ι (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : Jᵒᵖ) :
    (limitRightOpIsoOpColimit F).hom ≫ (colimit.ι F j).op = limit.π F.rightOp j.unop := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.unop` is the unopposite of `colimit F`. -/
@[to_dual /-- The colimit of `F.unop` is the unopposite of `limit F`. -/]
def limitUnopIsoUnopColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] :
    limit F.unop ≅ unop (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeUnopOfCocone _ (colimit.isColimit _)⟩

@[to_dual (attr := reassoc (attr := simp)) ι_comp_colimitUnopIsoUnopLimit_hom]
lemma limitUnopIsoUnopColimit_inv_comp_π (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : J) :
    (limitUnopIsoUnopColimit F).inv ≫ limit.π F.unop j = (colimit.ι F (op j)).unop := by
  simp [limitUnopIsoUnopColimit]

@[to_dual (attr := reassoc (attr := simp)) π_comp_colimitUnopIsoUnopLimit_inv]
lemma limitUnopIsoUnopColimit_hom_comp_ι (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ) :
    (limitUnopIsoUnopColimit F).hom ≫ (colimit.ι F j).unop = limit.π F.unop j.unop := by
  simp [← Iso.eq_inv_comp]

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
@[to_dual
/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.  -/]
instance hasLimitsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] :
    HasLimitsOfShape J Cᵒᵖ :=
  { has_limit := fun F => hasLimit_of_hasColimit_leftOp F }

@[to_dual]
theorem hasLimitsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasLimitsOfShape J C :=
  { has_limit := fun F => hasLimit_of_hasColimit_op F }

attribute [local instance] hasLimitsOfShape_op_of_hasColimitsOfShape

/-- If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
@[to_dual
/-- If `C` has limits, we can construct colimits for `Cᵒᵖ`. -/]
instance hasLimits_op_of_hasColimits [HasColimitsOfSize.{v₂, u₂} C] :
    HasLimitsOfSize.{v₂, u₂} Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩

@[to_dual]
theorem hasLimits_of_hasColimits_op [HasColimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasLimitsOfSize.{v₂, u₂} C :=
  { has_limits_of_shape := fun _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

@[deprecated (since := "2026-11-17")] alias colimitRightOpIsoUnopLimit := colimitRightOpIsoOpLimit

@[deprecated (since := "2026-11-17")]
alias ι_comp_colimitRightOpIsoUnopLimit_hom := ι_comp_colimitRightOpIsoOpLimit_hom

@[deprecated (since := "2026-11-17")]
alias π_comp_colimitRightOpIsoUnopLimit_inv := π_comp_colimitRightOpIsoOpLimit_inv

@[deprecated (since := "2026-11-17")] alias colimitUnopIsoOpLimit := colimitUnopIsoUnopLimit

@[deprecated (since := "2026-11-17")]
alias ι_comp_colimitUnopIsoOpLimit_hom := ι_comp_colimitUnopIsoUnopLimit_hom

@[deprecated (since := "2026-11-17")]
alias π_comp_colimitUnopIsoOpLimit_inv := π_comp_colimitUnopIsoUnopLimit_inv

@[to_dual]
lemma hasColimitsOfSize_opposite_iff :
    HasColimitsOfSize.{v₂, u₂} Cᵒᵖ ↔ HasLimitsOfSize.{v₂, u₂} C :=
  ⟨fun _ ↦ hasLimits_of_hasColimits_op, fun _ ↦ inferInstance⟩

@[to_dual]
instance hasFiniteColimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ :=
  ⟨fun _ _ _ => hasColimitsOfShape_op_of_hasLimitsOfShape⟩

@[to_dual]
lemma hasFiniteLimits_opposite_iff : HasFiniteLimits Cᵒᵖ ↔ HasFiniteColimits C :=
  ⟨fun _ ↦ ⟨fun _ _ _ ↦ hasColimitsOfShape_of_hasLimitsOfShape_op⟩, fun _ ↦ inferInstance⟩

@[to_dual]
lemma hasColimit_op_iff_hasLimit {F : J ⥤ C} : HasColimit F.op ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_hasColimit_op F, fun _ ↦ inferInstance⟩

@[to_dual]
lemma hasColimit_leftOp_iff_hasLimit {F : J ⥤ Cᵒᵖ} : HasColimit F.leftOp ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_hasColimit_leftOp F, fun _ ↦ inferInstance⟩

@[to_dual]
lemma hasColimit_rightOp_iff_hasLimit {F : Jᵒᵖ ⥤ C} : HasColimit F.rightOp ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_hasColimit_rightOp F, fun _ ↦ inferInstance⟩

@[to_dual]
lemma hasLimitsOfShape_opposite_iff : HasLimitsOfShape J Cᵒᵖ ↔ HasColimitsOfShape Jᵒᵖ C := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_of_hasLimitsOfShape_op

@[to_dual]
lemma hasLimitsOfShape_opposite_opposite_iff :
    HasLimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasColimitsOfShape J C := by
  refine ⟨fun _ ↦ hasColimitsOfShape_of_hasLimitsOfShape_op, fun _ ↦ ?_⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ C := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_op_of_hasColimitsOfShape

@[to_dual]
instance [HasWidePullbacks.{w} C] : HasWidePushouts.{w} Cᵒᵖ := by
  intro ι
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

@[to_dual]
lemma hasWidePullbacks_opposite_iff :
    HasWidePullbacks.{w} Cᵒᵖ ↔ HasWidePushouts.{w} C := by
  refine ⟨fun h ι ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

@[to_dual]
instance [HasFiniteWidePullbacks C] : HasFiniteWidePushouts Cᵒᵖ := by
  refine ⟨fun J _ ↦ ?_⟩
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

@[to_dual]
lemma hasFiniteWidePullbacks_opposite_iff :
    HasFiniteWidePullbacks Cᵒᵖ ↔ HasFiniteWidePushouts C := by
  refine ⟨fun h ↦ ⟨fun J _ ↦ ?_⟩, fun _ ↦ inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

end CategoryTheory.Limits
