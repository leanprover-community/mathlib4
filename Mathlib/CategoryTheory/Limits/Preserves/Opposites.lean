/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limit preservation properties of `Functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.leftOp` and `F.rightOp`
preserve certain (co)limits and vice versa.

-/


universe w w' v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

/-- If `F : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ Cᵒᵖ`. -/
def preservesLimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.op where
  preserves {_} hc :=
    isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` preserves
    limits of `K : J ⥤ C`. -/
def preservesLimitOfOp (K : J ⥤ C) (F : C ⥤ D) [PreservesColimit K.op F.op] :
    PreservesLimit K F where
  preserves {_} hc := isLimitOfOp (isColimitOfPreserves F.op (IsLimit.op hc))

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
    preserves limits of `K : J ⥤ Cᵒᵖ`. -/
def preservesLimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.leftOp where
  preserves {_} hc :=
    isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ C`. -/
def preservesLimitOfLeftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.op F.leftOp] :
    PreservesLimit K F where
  preserves {_} hc := isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.leftOp (IsLimit.op hc))

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ C`. -/
def preservesLimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F] :
    PreservesLimit K F.rightOp where
  preserves {_} hc :=
    isLimitConeRightOpOfCocone _ (isColimitOfPreserves F hc.op)

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ ⥤ D`
    preserves limits of `K : J ⥤ Cᵒᵖ`. -/
def preservesLimitOfRightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.leftOp F.rightOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    isLimitOfOp (isColimitOfPreserves F.rightOp (isColimitCoconeLeftOpOfCone _ hc))

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
    limits of `K : J ⥤ C`. -/
def preservesLimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] :
    PreservesLimit K F.unop where
  preserves {_} hc :=
    isLimitConeUnopOfCocone _ (isColimitOfPreserves F hc.op)

/-- If `F.unop : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ Cᵒᵖ`. -/
def preservesLimitOfUnop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F.unop] :
    PreservesLimit K F where
  preserves {_} hc :=
    isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.unop (isColimitCoconeLeftOpOfCone _ hc))

/-- If `F : C ⥤ D` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preservesColimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.op where
  preserves {_} hc :=
    isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` preserves
    colimits of `K : J ⥤ C`. -/
def preservesColimitOfOp (K : J ⥤ C) (F : C ⥤ D) [PreservesLimit K.op F.op] :
    PreservesColimit K F where
  preserves {_} hc := isColimitOfOp (isLimitOfPreserves F.op (IsColimit.op hc))

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preservesColimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.leftOp where
  preserves {_} hc :=
    isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ C`. -/
def preservesColimitOfLeftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.op F.leftOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.leftOp (IsColimit.op hc))

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ C`. -/
def preservesColimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F] :
    PreservesColimit K F.rightOp where
  preserves {_} hc :=
    isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F hc.op)

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D`
    preserves colimits of `K : J ⥤ Cᵒᵖ`. -/
def preservesColimitOfRightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.leftOp F.rightOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    isColimitOfOp (isLimitOfPreserves F.rightOp (isLimitConeLeftOpOfCocone _ hc))

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
    colimits of `K : J ⥤ C`. -/
def preservesColimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] :
    PreservesColimit K F.unop where
  preserves {_} hc :=
    isColimitCoconeUnopOfCone _ (isLimitOfPreserves F hc.op)

/-- If `F.unop : C ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preservesColimitOfUnop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F.unop] :
    PreservesColimit K F where
  preserves {_} hc :=
    isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.unop (isLimitConeLeftOpOfCocone _ hc))

section

variable (J)

/-- If `F : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of
    shape `J`. -/
def preservesLimitsOfShapeOp (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.op where preservesLimit {K} := preservesLimitOp K F

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits
    of shape `J`. -/
def preservesLimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.leftOp where preservesLimit {K} := preservesLimitLeftOp K F

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits
    of shape `J`. -/
def preservesLimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.rightOp where preservesLimit {K} := preservesLimitRightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves limits of
    shape `J`. -/
def preservesLimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.unop where preservesLimit {K} := preservesLimitUnop K F

/-- If `F : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of
    shape `J`. -/
def preservesColimitsOfShapeOp (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.op where preservesColimit {K} := preservesColimitOp K F

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.leftOp where preservesColimit {K} := preservesColimitLeftOp K F

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.rightOp where preservesColimit {K} := preservesColimitRightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.unop where preservesColimit {K} := preservesColimitUnop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserves limits
    of shape `J`. -/
def preservesLimitsOfShapeOfOp (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimitOfOp K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves limits
    of shape `J`. -/
def preservesLimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimitOfLeftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` preserves limits
    of shape `J`. -/
def preservesLimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimitOfRightOp K F

/-- If `F.unop : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits
    of shape `J`. -/
def preservesLimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimitOfUnop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeOfOp (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimitOfOp K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimitOfLeftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimitOfRightOp K F

/-- If `F.unop : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimitOfUnop K F

end

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsOfSizeOp (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits. -/
def preservesLimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
def preservesLimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeUnop _ _

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
def preservesColimitsOfSizeOp (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits. -/
def preservesColimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits. -/
def preservesColimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
def preservesColimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits. -/
def preservesLimitsOfSizeOfOp (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F.op] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.leftOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits. -/
def preservesLimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F.rightOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.unop] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOfUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits. -/
def preservesColimitsOfSizeOfOp (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F.op] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits. -/
def preservesColimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.leftOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits. -/
def preservesColimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F.rightOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
def preservesColimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.unop] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOfUnop _ _

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsOp (F : C ⥤ D) [PreservesColimits F] : PreservesLimits F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits. -/
def preservesLimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F] : PreservesLimits F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
def preservesLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeUnop _ _

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
def perservesColimitsOp (F : C ⥤ D) [PreservesLimits F] : PreservesColimits F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits. -/
def preservesColimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits. -/
def preservesColimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F] : PreservesColimits F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
def preservesColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits. -/
def preservesLimitsOfOp (F : C ⥤ D) [PreservesColimits F.op] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F.leftOp] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits. -/
def preservesLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F.rightOp] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F.unop] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShapeOfUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits. -/
def preservesColimitsOfOp (F : C ⥤ D) [PreservesLimits F.op] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits. -/
def preservesColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F.leftOp] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits. -/
def preservesColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F.rightOp] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
def preservesColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F.unop] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShapeOfUnop _ _

/-- If `F : C ⥤ D` preserves finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preservesFiniteLimitsOp (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.op where
  preservesFiniteLimits J _ _ := preservesLimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
    limits. -/
def preservesFiniteLimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.leftOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preservesFiniteLimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.rightOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F.unop : C ⥤ D` preserves finite
    limits. -/
def preservesFiniteLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.unop where
  preservesFiniteLimits J _ _ := preservesLimitsOfShapeUnop J F

/-- If `F : C ⥤ D` preserves finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preservesFiniteColimitsOp (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.op where
  preservesFiniteColimits J _ _ := preservesColimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
    colimits. -/
def preservesFiniteColimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.leftOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preservesFiniteColimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.rightOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F.unop : C ⥤ D` preserves finite
    colimits. -/
def preservesFiniteColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.unop where
  preservesFiniteColimits J _ _ := preservesColimitsOfShapeUnop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F : C ⥤ D` preserves finite limits. -/
def preservesFiniteLimitsOfOp (F : C ⥤ D) [PreservesFiniteColimits F.op] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShapeOfOp J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite colimits, then `F : C ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preservesFiniteLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F.leftOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShapeOfLeftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite colimits, then `F : Cᵒᵖ ⥤ D` preserves finite
    limits. -/
def preservesFiniteLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F.rightOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShapeOfRightOp J F

/-- If `F.unop : C ⥤ D` preserves finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits. -/
def preservesFiniteLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F.unop] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShapeOfUnop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F : C ⥤ D` preserves finite colimits. -/
def preservesFiniteColimitsOfOp (F : C ⥤ D) [PreservesFiniteLimits F.op] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShapeOfOp J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite limits, then `F : C ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preservesFiniteColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F.leftOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShapeOfLeftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite limits, then `F : Cᵒᵖ ⥤ D` preserves finite
    colimits. -/
def preservesFiniteColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F.rightOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShapeOfRightOp J F

/-- If `F.unop : C ⥤ D` preserves finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits. -/
def preservesFiniteColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F.unop] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShapeOfUnop J F


/-- If `F : C ⥤ D` preserves finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    products. -/
def preservesFiniteProductsOp (F : C ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.op where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShapeOp
    exact preservesColimitsOfShapeOfEquiv (Discrete.opposite J).symm _

/-- If `F : C ⥤ Dᵒᵖ` preserves finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
    products. -/
def preservesFiniteProductsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.leftOp where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShapeLeftOp
    exact preservesColimitsOfShapeOfEquiv (Discrete.opposite J).symm _

/-- If `F : Cᵒᵖ ⥤ D` preserves finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
    products. -/
def preservesFiniteProductsRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.rightOp where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShapeRightOp
    exact preservesColimitsOfShapeOfEquiv (Discrete.opposite J).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite coproducts, then `F.unop : C ⥤ D` preserves finite
    products. -/
def preservesFiniteProductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.unop where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShapeUnop
    exact preservesColimitsOfShapeOfEquiv (Discrete.opposite J).symm _

/-- If `F : C ⥤ D` preserves finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    coproducts. -/
def preservesFiniteCoproductsOp (F : C ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.op where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesColimitsOfShapeOp
    exact preservesLimitsOfShapeOfEquiv (Discrete.opposite J).symm _

/-- If `F : C ⥤ Dᵒᵖ` preserves finite products, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
    coproducts. -/
def preservesFiniteCoproductsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.leftOp where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesColimitsOfShapeLeftOp
    exact preservesLimitsOfShapeOfEquiv (Discrete.opposite J).symm _

/-- If `F : Cᵒᵖ ⥤ D` preserves finite products, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
    coproducts. -/
def preservesFiniteCoproductsRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.rightOp where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesColimitsOfShapeRightOp
    exact preservesLimitsOfShapeOfEquiv (Discrete.opposite J).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite products, then `F.unop : C ⥤ D` preserves finite
    coproducts. -/
def preservesFiniteCoproductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.unop where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesColimitsOfShapeUnop
    exact preservesLimitsOfShapeOfEquiv (Discrete.opposite J).symm _

end CategoryTheory.Limits
