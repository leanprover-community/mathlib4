/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limit preservation properties of `Functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.leftOp` and `F.rightOp`
preserve certain (co)limits and vice versa.

-/

public section


universe w w' v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

/-- If `F : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.op where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` preserves
limits of `K : J ⥤ C`. -/
lemma preservesLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesColimit K.op F.op] :
    PreservesLimit K F where
  preserves {_} hc := ⟨isLimitOfOp (isColimitOfPreserves F.op (IsLimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
preserves limits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.leftOp where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ C`. -/
lemma preservesLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.op F.leftOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.leftOp (IsLimit.op hc))⟩

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ C`. -/
lemma preservesLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F] :
    PreservesLimit K F.rightOp where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F hc.op)⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ ⥤ D`
preserves limits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.leftOp F.rightOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfOp (isColimitOfPreserves F.rightOp (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
limits of `K : J ⥤ C`. -/
lemma preservesLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] :
    PreservesLimit K F.unop where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F hc.op)⟩

/-- If `F.unop : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F.unop] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F : C ⥤ D` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.op where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` preserves
colimits of `K : J ⥤ C`. -/
lemma preservesColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesLimit K.op F.op] :
    PreservesColimit K F where
  preserves {_} hc := ⟨isColimitOfOp (isLimitOfPreserves F.op (IsColimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.leftOp where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ C`. -/
lemma preservesColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.op F.leftOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.leftOp (IsColimit.op hc))⟩

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ C`. -/
lemma preservesColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F] :
    PreservesColimit K F.rightOp where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F hc.op)⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D`
preserves colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.leftOp F.rightOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfOp (isLimitOfPreserves F.rightOp (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
colimits of `K : J ⥤ C`. -/
lemma preservesColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] :
    PreservesColimit K F.unop where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F hc.op)⟩

/-- If `F.unop : C ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F.unop] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

section

variable (J)

/-- If `F : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of
shape `J`. -/
lemma preservesLimitsOfShape_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.op where preservesLimit {K} := preservesLimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.leftOp where preservesLimit {K} := preservesLimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.rightOp where preservesLimit {K} := preservesLimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves limits of
shape `J`. -/
lemma preservesLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.unop where preservesLimit {K} := preservesLimit_unop K F

/-- If `F : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of
shape `J`. -/
lemma preservesColimitsOfShape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.op where preservesColimit {K} := preservesColimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.leftOp where preservesColimit {K} := preservesColimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.rightOp where preservesColimit {K} := preservesColimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.unop where preservesColimit {K} := preservesColimit_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_of_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_of_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_unop K F

end

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimitsOfSize_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits. -/
lemma preservesLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
lemma preservesLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimitsOfSize_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits. -/
lemma preservesColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
lemma preservesColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits. -/
lemma preservesLimitsOfSize_of_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F.op] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.leftOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits. -/
lemma preservesLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F.rightOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.unop] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits. -/
lemma preservesColimitsOfSize_of_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F.op] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.leftOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits. -/
lemma preservesColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F.rightOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.unop] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimits_op (F : C ⥤ D) [PreservesColimits F] : PreservesLimits F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits. -/
lemma preservesLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F] : PreservesLimits F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
lemma preservesLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimits_op (F : C ⥤ D) [PreservesLimits F] : PreservesColimits F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits. -/
lemma preservesColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F] :
    PreservesColimits F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
lemma preservesColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits. -/
lemma preservesLimits_of_op (F : C ⥤ D) [PreservesColimits F.op] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F.leftOp] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits. -/
lemma preservesLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F.rightOp] :
    PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F.unop] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits. -/
lemma preservesColimits_of_op (F : C ⥤ D) [PreservesLimits F.op] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F.leftOp] :
    PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits. -/
lemma preservesColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F.rightOp] :
    PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F.unop] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` preserves finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
limits. -/
lemma preservesFiniteLimits_op (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.op where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
limits. -/
lemma preservesFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.leftOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
limits. -/
lemma preservesFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.rightOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F.unop : C ⥤ D` preserves finite
limits. -/
lemma preservesFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.unop where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_unop J F

/-- If `F : C ⥤ D` preserves finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
colimits. -/
lemma preservesFiniteColimits_op (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.op where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
colimits. -/
lemma preservesFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.leftOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
colimits. -/
lemma preservesFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.rightOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F.unop : C ⥤ D` preserves finite
colimits. -/
lemma preservesFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.unop where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F : C ⥤ D` preserves finite limits. -/
lemma preservesFiniteLimits_of_op (F : C ⥤ D) [PreservesFiniteColimits F.op] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite colimits, then `F : C ⥤ Dᵒᵖ` preserves finite
limits. -/
lemma preservesFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F.leftOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite colimits, then `F : Cᵒᵖ ⥤ D` preserves finite
limits. -/
lemma preservesFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F.rightOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` preserves finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits. -/
lemma preservesFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F.unop] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F : C ⥤ D` preserves finite colimits. -/
lemma preservesFiniteColimits_of_op (F : C ⥤ D) [PreservesFiniteLimits F.op] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite limits, then `F : C ⥤ Dᵒᵖ` preserves finite
colimits. -/
lemma preservesFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F.leftOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite limits, then `F : Cᵒᵖ ⥤ D` preserves finite
colimits. -/
lemma preservesFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F.rightOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` preserves finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits. -/
lemma preservesFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F.unop] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_unop J F

/-- If `F : C ⥤ D` preserves finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
products. -/
lemma preservesFiniteProducts_op (F : C ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.op where
  preserves n := by
    apply +allowSynthFailures preservesLimitsOfShape_op
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` preserves finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
products. -/
lemma preservesFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.leftOp where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_leftOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` preserves finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
products. -/
lemma preservesFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.rightOp where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_rightOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite coproducts, then `F.unop : C ⥤ D` preserves finite
products. -/
lemma preservesFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.unop where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_unop
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` preserves finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
coproducts. -/
lemma preservesFiniteCoproducts_op (F : C ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.op where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_op
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` preserves finite products, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
coproducts. -/
lemma preservesFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.leftOp where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_leftOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` preserves finite products, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
coproducts. -/
lemma preservesFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.rightOp where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_rightOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite products, then `F.unop : C ⥤ D` preserves finite
coproducts. -/
lemma preservesFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.unop where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_unop
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects
limits of `K : J ⥤ Cᵒᵖ`. -/
lemma reflectsLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsColimit K.leftOp F] :
    ReflectsLimit K F.op where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ <| isColimitOfReflects F (isColimitCoconeLeftOpOfCone _ hc)⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` reflects
limits of `K : J ⥤ C`. -/
lemma reflectsLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [ReflectsColimit K.op F.op] :
    ReflectsLimit K F where
  reflects {_} hc := ⟨isLimitOfOp (isColimitOfReflects F.op (IsLimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
reflects limits of `K : J ⥤ Cᵒᵖ`. -/
lemma reflectsLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F] :
    ReflectsLimit K F.leftOp where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ <| isColimitOfReflects F hc.op⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` reflects
limits of `K : J ⥤ C`. -/
lemma reflectsLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.op F.leftOp] :
    ReflectsLimit K F where
  reflects {_} hc :=
    ⟨isLimitOfOp <|
      isColimitOfReflects F.leftOp (isColimitOfConeRightOpOfCocone _ hc)⟩

/-- If `F : Cᵒᵖ ⥤ D` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` reflects
limits of `K : J ⥤ C`. -/
lemma reflectsLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.op F] :
    ReflectsLimit K F.rightOp where
  reflects {_} hc :=
    ⟨isLimitOfOp <| isColimitOfReflects F <| isColimitOfConeRightOpOfCocone _ hc⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ ⥤ D`
reflects limits of `K : J ⥤ Cᵒᵖ`. -/
lemma reflectsLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.leftOp F.rightOp] :
    ReflectsLimit K F where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ <| isColimitOfReflects F.rightOp <|
      isColimitOfConeUnopOfCocone _ hc⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` reflects
limits of `K : J ⥤ C`. -/
lemma reflectsLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.op F] :
    ReflectsLimit K F.unop where
  reflects {_} hc := ⟨isLimitOfOp (isColimitOfReflects F hc.op)⟩

/-- If `F.unop : C ⥤ D` reflects colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects
limits of `K : J ⥤ Cᵒᵖ`. -/
lemma reflectsLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F.unop] :
    ReflectsLimit K F where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfReflects F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F : C ⥤ D` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma reflectsColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsLimit K.leftOp F] :
    ReflectsColimit K F.op where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` reflects
colimits of `K : J ⥤ C`. -/
lemma reflectsColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [ReflectsLimit K.op F.op] :
    ReflectsColimit K F where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F.op (IsColimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` reflects
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma reflectsColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F] :
    ReflectsColimit K F.leftOp where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitOfCoconeUnopOfCone _ hc))⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` reflects
colimits of `K : J ⥤ C`. -/
lemma reflectsColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.op F.leftOp] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfOp (isLimitOfReflects F.leftOp <| isLimitOfCoconeRightOpOfCone _ hc)⟩

/-- If `F : Cᵒᵖ ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` reflects
colimits of `K : J ⥤ C`. -/
lemma reflectsColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.op F] :
    ReflectsColimit K F.rightOp where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F <| isLimitOfCoconeRightOpOfCone _ hc)⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D`
reflects colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma reflectsColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.leftOp F.rightOp] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.rightOp hc.op)⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` reflects
colimits of `K : J ⥤ C`. -/
lemma reflectsColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.op F] :
    ReflectsColimit K F.unop where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F hc.op)⟩

/-- If `F.unop : C ⥤ D` reflects limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma reflectsColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F.unop] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

section

variable (J)

/-- If `F : C ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of
shape `J`. -/
lemma reflectsLimitsOfShape_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.op where reflectsLimit {K} := reflectsLimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` reflects limits
of shape `J`. -/
lemma reflectsLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.leftOp where reflectsLimit {K} := reflectsLimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` reflects limits
of shape `J`. -/
lemma reflectsLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.rightOp where reflectsLimit {K} := reflectsLimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` reflects limits of
shape `J`. -/
lemma reflectsLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.unop where reflectsLimit {K} := reflectsLimit_unop K F

/-- If `F : C ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of
shape `J`. -/
lemma reflectsColimitsOfShape_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.op where reflectsColimit {K} := reflectsColimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits
of shape `J`. -/
lemma reflectsColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.leftOp where reflectsColimit {K} := reflectsColimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits
of shape `J`. -/
lemma reflectsColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.rightOp where reflectsColimit {K} := reflectsColimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` reflects colimits
of shape `J`. -/
lemma reflectsColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.unop where reflectsColimit {K} := reflectsColimit_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` reflects limits
of shape `J`. -/
lemma reflectsLimitsOfShape_of_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.op] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` reflects limits
of shape `J`. -/
lemma reflectsLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.leftOp] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` reflects limits
of shape `J`. -/
lemma reflectsLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.rightOp] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` reflects colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits
of shape `J`. -/
lemma reflectsLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.unop] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F : C ⥤ D` reflects colimits
of shape `J`. -/
lemma reflectsColimitsOfShape_of_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.op] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` reflects colimits
of shape `J`. -/
lemma reflectsColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.leftOp] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` reflects colimits
of shape `J`. -/
lemma reflectsColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.rightOp] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` reflects limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits
of shape `J`. -/
lemma reflectsColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.unop] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_unop K F

end

/-- If `F : C ⥤ D` reflects colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits. -/
lemma reflectsLimitsOfSize_op (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.op where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` reflects colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects limits. -/
lemma reflectsLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.leftOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` reflects colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects limits. -/
lemma reflectsLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.rightOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F.unop : C ⥤ D` reflects limits. -/
lemma reflectsLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.unop where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` reflects limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits. -/
lemma reflectsColimitsOfSize_op (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.op where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` reflects limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits. -/
lemma reflectsColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.leftOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` reflects limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits. -/
lemma reflectsColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.rightOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F.unop : C ⥤ D` reflects colimits. -/
lemma reflectsColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.unop where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F : C ⥤ D` reflects limits. -/
lemma reflectsLimitsOfSize_of_op (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.op] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits, then `F : C ⥤ Dᵒᵖ` reflects limits. -/
lemma reflectsLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.leftOp] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits, then `F : Cᵒᵖ ⥤ D` reflects limits. -/
lemma reflectsLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.rightOp] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` reflects colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits. -/
lemma reflectsLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.unop] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F : C ⥤ D` reflects colimits. -/
lemma reflectsColimitsOfSize_of_op (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.op] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits, then `F : C ⥤ Dᵒᵖ` reflects colimits. -/
lemma reflectsColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.leftOp] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits, then `F : Cᵒᵖ ⥤ D` reflects colimits. -/
lemma reflectsColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.rightOp] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` reflects limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits. -/
lemma reflectsColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.unop] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` reflects colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits. -/
lemma reflectsLimits_op (F : C ⥤ D) [ReflectsColimits F] : ReflectsLimits F.op where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` reflects colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects limits. -/
lemma reflectsLimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimits F] : ReflectsLimits F.leftOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` reflects colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects limits. -/
lemma reflectsLimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimits F] : ReflectsLimits F.rightOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F.unop : C ⥤ D` reflects limits. -/
lemma reflectsLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F] : ReflectsLimits F.unop where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` reflects limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits. -/
lemma reflectsColimits_op (F : C ⥤ D) [ReflectsLimits F] : ReflectsColimits F.op where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` reflects limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits. -/
lemma reflectsColimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimits F] : ReflectsColimits F.leftOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` reflects limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits. -/
lemma reflectsColimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimits F] :
    ReflectsColimits F.rightOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F.unop : C ⥤ D` reflects colimits. -/
lemma reflectsColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F] : ReflectsColimits F.unop where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits, then `F : C ⥤ D` reflects limits. -/
lemma reflectsLimits_of_op (F : C ⥤ D) [ReflectsColimits F.op] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects colimits, then `F : C ⥤ Dᵒᵖ` reflects limits. -/
lemma reflectsLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimits F.leftOp] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects colimits, then `F : Cᵒᵖ ⥤ D` reflects limits. -/
lemma reflectsLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimits F.rightOp] :
    ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` reflects colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits. -/
lemma reflectsLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F.unop] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects limits, then `F : C ⥤ D` reflects colimits. -/
lemma reflectsColimits_of_op (F : C ⥤ D) [ReflectsLimits F.op] : ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects limits, then `F : C ⥤ Dᵒᵖ` reflects colimits. -/
lemma reflectsColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimits F.leftOp] :
    ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects limits, then `F : Cᵒᵖ ⥤ D` reflects colimits. -/
lemma reflectsColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimits F.rightOp] :
    ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` reflects limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects colimits. -/
lemma reflectsColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F.unop] : ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` reflects finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
limits. -/
lemma reflectsFiniteLimits_op (F : C ⥤ D) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.op where
  reflects J _ _ := reflectsLimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` reflects finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects finite
limits. -/
lemma reflectsFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.leftOp where
  reflects J _ _ := reflectsLimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` reflects finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects finite
limits. -/
lemma reflectsFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.rightOp where
  reflects J _ _ := reflectsLimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite colimits, then `F.unop : C ⥤ D` reflects finite
limits. -/
lemma reflectsFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.unop where
  reflects J _ _ := reflectsLimitsOfShape_unop J F

/-- If `F : C ⥤ D` reflects finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
colimits. -/
lemma reflectsFiniteColimits_op (F : C ⥤ D) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.op where
  reflects J _ _ := reflectsColimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` reflects finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` reflects finite
colimits. -/
lemma reflectsFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.leftOp where
  reflects J _ _ := reflectsColimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` reflects finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` reflects finite
colimits. -/
lemma reflectsFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.rightOp where
  reflects J _ _ := reflectsColimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite limits, then `F.unop : C ⥤ D` reflects finite
colimits. -/
lemma reflectsFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.unop where
  reflects J _ _ := reflectsColimitsOfShape_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite colimits, then `F : C ⥤ D` reflects finite limits. -/
lemma reflectsFiniteLimits_of_op (F : C ⥤ D) [ReflectsFiniteColimits F.op] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects finite colimits, then `F : C ⥤ Dᵒᵖ` reflects finite
limits. -/
lemma reflectsFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.leftOp] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects finite colimits, then `F : Cᵒᵖ ⥤ D` reflects finite
limits. -/
lemma reflectsFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F.rightOp] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` reflects finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite limits. -/
lemma reflectsFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.unop] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite limits, then `F : C ⥤ D` reflects finite colimits. -/
lemma reflectsFiniteColimits_of_op (F : C ⥤ D) [ReflectsFiniteLimits F.op] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` reflects finite limits, then `F : C ⥤ Dᵒᵖ` reflects finite
colimits. -/
lemma reflectsFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.leftOp] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` reflects finite limits, then `F : Cᵒᵖ ⥤ D` reflects finite
colimits. -/
lemma reflectsFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F.rightOp] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` reflects finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite colimits. -/
lemma reflectsFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.unop] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_unop J F

/-- If `F : C ⥤ D` reflects finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
products. -/
lemma reflectsFiniteProducts_op (F : C ⥤ D) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.op where
  reflects n := by
    apply +allowSynthFailures reflectsLimitsOfShape_op
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` reflects finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` reflects finite
products. -/
lemma reflectsFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.leftOp where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_leftOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` reflects finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` reflects finite
products. -/
lemma reflectsFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.rightOp where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_rightOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite coproducts, then `F.unop : C ⥤ D` reflects finite
products. -/
lemma reflectsFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.unop where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_unop
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` reflects finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite
coproducts. -/
lemma reflectsFiniteCoproducts_op (F : C ⥤ D) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.op where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_op
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` reflects finite products, then `F.leftOp : Cᵒᵖ ⥤ D` reflects finite
coproducts. -/
lemma reflectsFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.leftOp where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_leftOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` reflects finite products, then `F.rightOp : C ⥤ Dᵒᵖ` reflects finite
coproducts. -/
lemma reflectsFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.rightOp where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_rightOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` reflects finite products, then `F.unop : C ⥤ D` reflects finite
coproducts. -/
lemma reflectsFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.unop where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_unop
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

end CategoryTheory.Limits
