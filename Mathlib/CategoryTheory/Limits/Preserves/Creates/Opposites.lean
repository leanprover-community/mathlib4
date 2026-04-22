/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite

/-!
# Limit creation properties of `Functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.leftOp` and `F.rightOp`
create certain (co)limits and vice versa.

-/

public section

universe w w' v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

namespace Limits

/-- If `F : C ⥤ D` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates
limits of `K : J ⥤ Cᵒᵖ`. -/
@[implicit_reducible]
def createsLimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesColimit K.leftOp F] :
    CreatesLimit K F.op where
  __ := reflectsLimit_op _ _
  lifts _ hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F) _ (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` creates
limits of `K : J ⥤ C`. -/
@[implicit_reducible]
def createsLimitOfOp (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K.op F.op] :
    CreatesLimit K F where
  __ := reflectsLimit_of_op _ _
  lifts _ hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F.op) _ hc.op
    { liftedCone := lc.liftedCocone.unop
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F : C ⥤ Dᵒᵖ` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
creates limits of `K : J ⥤ Cᵒᵖ`. -/
@[implicit_reducible]
def createsLimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F] :
    CreatesLimit K F.leftOp where
  __ := reflectsLimit_leftOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F) c.op hc.op
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates
limits of `K : J ⥤ C`. -/
@[implicit_reducible]
def createsLimitOfLeftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.op F.leftOp] :
    CreatesLimit K F where
  __ := reflectsLimit_of_leftOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F.leftOp)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := lc.liftedCocone.unop
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F : Cᵒᵖ ⥤ D` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates
limits of `K : J ⥤ C`. -/
@[implicit_reducible]
def createsLimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.op F] :
    CreatesLimit K F.rightOp where
  __ := reflectsLimit_rightOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := lc.liftedCocone.unop
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D`
creates limits of `K : J ⥤ Cᵒᵖ`. -/
@[implicit_reducible]
def createsLimitOfRightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.leftOp F.rightOp] :
    CreatesLimit K F where
  __ := reflectsLimit_of_rightOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F.rightOp) c.op hc.op
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` creates
limits of `K : J ⥤ C`. -/
@[implicit_reducible]
def createsLimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.op F] :
    CreatesLimit K F.unop where
  __ := reflectsLimit_unop _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F) c.op hc.op
    { liftedCone := lc.liftedCocone.unop
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F.unop : C ⥤ D` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates
limits of `K : J ⥤ Cᵒᵖ`. -/
@[implicit_reducible]
def createsLimitOfUnop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F.unop] :
    CreatesLimit K F where
  __ := reflectsLimit_of_unop _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F.unop)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F : C ⥤ D` creates limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates
colimits of `K : J ⥤ Cᵒᵖ`. -/
@[implicit_reducible]
def createsColimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesLimit K.leftOp F] :
    CreatesColimit K F.op where
  __ := reflectsColimit_op _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` creates
colimits of `K : J ⥤ C`. -/
@[implicit_reducible]
def createsColimitOfOp (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K.op F.op] :
    CreatesColimit K F where
  __ := reflectsColimit_of_op _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F.op) c.op hc.op
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F : C ⥤ Dᵒᵖ` creates limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` creates
colimits of `K : J ⥤ Cᵒᵖ`. -/
@[implicit_reducible]
def createsColimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F] :
    CreatesColimit K F.leftOp where
  __ := reflectsColimit_leftOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F) c.op hc.op
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates
colimits of `K : J ⥤ C`. -/
@[implicit_reducible]
def createsColimitOfLeftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.op F.leftOp] :
    CreatesColimit K F where
  __ := reflectsColimit_of_leftOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F.leftOp)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F : Cᵒᵖ ⥤ D` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates
colimits of `K : J ⥤ C`. -/
@[implicit_reducible]
def createsColimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.op F] :
    CreatesColimit K F.rightOp where
  __ := reflectsColimit_rightOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D`
creates colimits of `K : J ⥤ Cᵒᵖ`. -/
@[implicit_reducible]
def createsColimitOfRightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.leftOp F.rightOp] :
    CreatesColimit K F where
  __ := reflectsColimit_of_rightOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F.rightOp) c.op hc.op
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` creates
colimits of `K : J ⥤ C`. -/
@[implicit_reducible]
def createsColimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.op F] :
    CreatesColimit K F.unop where
  __ := reflectsColimit_unop _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F) c.op hc.op
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F.unop : C ⥤ D` creates limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates
colimits of `K : J ⥤ Cᵒᵖ`. -/
@[implicit_reducible]
def createsColimitOfUnop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F.unop] :
    CreatesColimit K F where
  __ := reflectsColimit_of_unop _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F.unop)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

section

variable (J)

/-- If `F : C ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of
shape `J`. -/
@[implicit_reducible]
def createsLimitsOfShapeOp (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.op where CreatesLimit {K} := createsLimitOp K F

/-- If `F : C ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits
of shape `J`. -/
@[implicit_reducible]
def createsLimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.leftOp where CreatesLimit {K} := createsLimitLeftOp K F

/-- If `F : Cᵒᵖ ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[implicit_reducible]
def createsLimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.rightOp where CreatesLimit {K} := createsLimitRightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` creates limits of
shape `J`. -/
@[implicit_reducible]
def createsLimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.unop where CreatesLimit {K} := createsLimitUnop K F

/-- If `F : C ⥤ D` creates limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of
shape `J`. -/
@[implicit_reducible]
def createsColimitsOfShapeOp (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.op where CreatesColimit {K} := createsColimitOp K F

/-- If `F : C ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits
of shape `J`. -/
@[implicit_reducible]
def createsColimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.leftOp where CreatesColimit {K} := createsColimitLeftOp K F

/-- If `F : Cᵒᵖ ⥤ D` creates limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[implicit_reducible]
def createsColimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.rightOp where CreatesColimit {K} := createsColimitRightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` creates colimits
of shape `J`. -/
@[implicit_reducible]
def createsColimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.unop where CreatesColimit {K} := createsColimitUnop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` creates limits
of shape `J`. -/
@[implicit_reducible]
def createsLimitsOfShapeOfOp (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.op] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfOp K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[implicit_reducible]
def createsLimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.leftOp] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfLeftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` creates limits
of shape `J`. -/
@[implicit_reducible]
def createsLimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.rightOp] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfRightOp K F

/-- If `F.unop : C ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[implicit_reducible]
def createsLimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.unop] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfUnop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F : C ⥤ D` creates colimits
of shape `J`. -/
@[implicit_reducible]
def createsColimitsOfShapeOfOp (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.op] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfOp K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[implicit_reducible]
def createsColimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.leftOp] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfLeftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` creates colimits
of shape `J`. -/
@[implicit_reducible]
def createsColimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.rightOp] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfRightOp K F

/-- If `F.unop : C ⥤ D` creates limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[implicit_reducible]
def createsColimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.unop] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfUnop K F

end

/-- If `F : C ⥤ D` creates colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
@[implicit_reducible]
def createsLimitsOfSizeOp (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.op where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` creates colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits. -/
@[implicit_reducible]
def createsLimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.leftOp where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` creates colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits. -/
@[implicit_reducible]
def createsLimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.rightOp where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F.unop : C ⥤ D` creates limits. -/
@[implicit_reducible]
def createsLimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.unop where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeUnop _ _

/-- If `F : C ⥤ D` creates limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
@[implicit_reducible]
def createsColimitsOfSizeOp (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.op where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` creates limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits. -/
@[implicit_reducible]
def createsColimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.leftOp where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` creates limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits. -/
@[implicit_reducible]
def createsColimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.rightOp where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F.unop : C ⥤ D` creates colimits. -/
@[implicit_reducible]
def createsColimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.unop where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F : C ⥤ D` creates limits. -/
@[implicit_reducible]
def createsLimitsOfSizeOfOp (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F.op] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits, then `F : C ⥤ Dᵒᵖ` creates limits. -/
@[implicit_reducible]
def createsLimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.leftOp] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits, then `F : Cᵒᵖ ⥤ D` creates limits. -/
@[implicit_reducible]
def createsLimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F.rightOp] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` creates colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
@[implicit_reducible]
def createsLimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.unop] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F : C ⥤ D` creates colimits. -/
@[implicit_reducible]
def createsColimitsOfSizeOfOp (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F.op] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits, then `F : C ⥤ Dᵒᵖ` creates colimits. -/
@[implicit_reducible]
def createsColimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.leftOp] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits, then `F : Cᵒᵖ ⥤ D` creates colimits. -/
@[implicit_reducible]
def createsColimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F.rightOp] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` creates limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
@[implicit_reducible]
def createsColimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.unop] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfUnop _ _

/-- If `F : C ⥤ D` creates colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
abbrev createsLimitsOp (F : C ⥤ D) [CreatesColimits F] : CreatesLimits F.op :=
  createsLimitsOfSizeOp F

/-- If `F : C ⥤ Dᵒᵖ` creates colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits. -/
abbrev createsLimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.leftOp :=
  createsLimitsOfSizeLeftOp F

/-- If `F : Cᵒᵖ ⥤ D` creates colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits. -/
abbrev createsLimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F] : CreatesLimits F.rightOp :=
  createsLimitsOfSizeRightOp F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F.unop : C ⥤ D` creates limits. -/
abbrev createsLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.unop :=
  createsLimitsOfSizeUnop F

/-- If `F : C ⥤ D` creates limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
abbrev createsColimitsOp (F : C ⥤ D) [CreatesLimits F] : CreatesColimits F.op :=
  createsColimitsOfSizeOp F

/-- If `F : C ⥤ Dᵒᵖ` creates limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits. -/
abbrev createsColimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.leftOp :=
  createsColimitsOfSizeLeftOp F

/-- If `F : Cᵒᵖ ⥤ D` creates limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits. -/
abbrev createsColimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F] : CreatesColimits F.rightOp :=
  createsColimitsOfSizeRightOp F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F.unop : C ⥤ D` creates colimits. -/
abbrev createsColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.unop :=
  createsColimitsOfSizeUnop F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F : C ⥤ D` creates limits. -/
abbrev createsLimitsOfOp (F : C ⥤ D) [CreatesColimits F.op] : CreatesLimits F :=
  createsLimitsOfSizeOfOp F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits, then `F : C ⥤ Dᵒᵖ` creates limits. -/
abbrev createsLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F.leftOp] : CreatesLimits F :=
  createsLimitsOfSizeOfLeftOp F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits, then `F : Cᵒᵖ ⥤ D` creates limits. -/
abbrev createsLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F.rightOp] : CreatesLimits F :=
  createsLimitsOfSizeOfRightOp F

/-- If `F.unop : C ⥤ D` creates colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
abbrev createsLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F.unop] : CreatesLimits F :=
  createsLimitsOfSizeOfUnop F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F : C ⥤ D` creates colimits. -/
abbrev createsColimitsOfOp (F : C ⥤ D) [CreatesLimits F.op] : CreatesColimits F :=
  createsColimitsOfSizeOfOp F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits, then `F : C ⥤ Dᵒᵖ` creates colimits. -/
abbrev createsColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F.leftOp] : CreatesColimits F :=
  createsColimitsOfSizeOfLeftOp F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits, then `F : Cᵒᵖ ⥤ D` creates colimits. -/
abbrev createsColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F.rightOp] : CreatesColimits F :=
  createsColimitsOfSizeOfRightOp F

/-- If `F.unop : C ⥤ D` creates limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
abbrev createsColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F.unop] : CreatesColimits F :=
  createsColimitsOfSizeOfUnop F

/-- If `F : C ⥤ D` creates finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
limits. -/
@[implicit_reducible]
def createsFiniteLimitsOp (F : C ⥤ D) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.op where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` creates finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
limits. -/
@[implicit_reducible]
def createsFiniteLimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.leftOp where
  createsFiniteLimits J _ _ := createsLimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` creates finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
limits. -/
@[implicit_reducible]
def createsFiniteLimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.rightOp where
  createsFiniteLimits J _ _ := createsLimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits, then `F.unop : C ⥤ D` creates finite
limits. -/
@[implicit_reducible]
def createsFiniteLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.unop where
  createsFiniteLimits J _ _ := createsLimitsOfShapeUnop J F

/-- If `F : C ⥤ D` creates finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
colimits. -/
@[implicit_reducible]
def createsFiniteColimitsOp (F : C ⥤ D) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.op where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` creates finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
colimits. -/
@[implicit_reducible]
def createsFiniteColimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.leftOp where
  createsFiniteColimits J _ _ := createsColimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` creates finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
colimits. -/
@[implicit_reducible]
def createsFiniteColimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.rightOp where
  createsFiniteColimits J _ _ := createsColimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits, then `F.unop : C ⥤ D` creates finite
colimits. -/
@[implicit_reducible]
def createsFiniteColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.unop where
  createsFiniteColimits J _ _ := createsColimitsOfShapeUnop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits, then `F : C ⥤ D` creates finite limits. -/
@[implicit_reducible]
def createsFiniteLimitsOfOp (F : C ⥤ D) [CreatesFiniteColimits F.op] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfOp J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates finite colimits, then `F : C ⥤ Dᵒᵖ` creates finite
limits. -/
@[implicit_reducible]
def createsFiniteLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F.leftOp] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfLeftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates finite colimits, then `F : Cᵒᵖ ⥤ D` creates finite
limits. -/
@[implicit_reducible]
def createsFiniteLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F.rightOp] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfRightOp J F

/-- If `F.unop : C ⥤ D` creates finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits. -/
@[implicit_reducible]
def createsFiniteLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F.unop] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfUnop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits, then `F : C ⥤ D` creates finite colimits. -/
@[implicit_reducible]
def createsFiniteColimitsOfOp (F : C ⥤ D) [CreatesFiniteLimits F.op] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfOp J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates finite limits, then `F : C ⥤ Dᵒᵖ` creates finite
colimits. -/
@[implicit_reducible]
def createsFiniteColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F.leftOp] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfLeftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates finite limits, then `F : Cᵒᵖ ⥤ D` creates finite
colimits. -/
@[implicit_reducible]
def createsFiniteColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F.rightOp] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfRightOp J F

/-- If `F.unop : C ⥤ D` creates finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits. -/
@[implicit_reducible]
def createsFiniteColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F.unop] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfUnop J F

/-- If `F : C ⥤ D` creates finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
products. -/
@[implicit_reducible]
def createsFiniteProductsOp (F : C ⥤ D) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.op where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` creates finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
products. -/
@[implicit_reducible]
def createsFiniteProductsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.leftOp where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeLeftOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` creates finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
products. -/
@[implicit_reducible]
def createsFiniteProductsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.rightOp where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeRightOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite coproducts, then `F.unop : C ⥤ D` creates finite
products. -/
@[implicit_reducible]
def createsFiniteProductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.unop where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeUnop
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` creates finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
coproducts. -/
@[implicit_reducible]
def createsFiniteCoproductsOp (F : C ⥤ D) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.op where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` creates finite products, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
coproducts. -/
@[implicit_reducible]
def createsFiniteCoproductsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.leftOp where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeLeftOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` creates finite products, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
coproducts. -/
@[implicit_reducible]
def createsFiniteCoproductsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.rightOp where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeRightOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite products, then `F.unop : C ⥤ D` creates finite
coproducts. -/
@[implicit_reducible]
def createsFiniteCoproductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.unop where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeUnop
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

end CategoryTheory.Limits
