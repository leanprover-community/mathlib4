/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Limit creation properties of `Functor.op` and related constructions

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
lemma preservesLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesColimit K.leftOp F] :
    CreatesLimit K F.op where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfCreates F (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` preserves
limits of `K : J ⥤ C`. -/
lemma preservesLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K.op F.op] :
    CreatesLimit K F where
  preserves {_} hc := ⟨isLimitOfOp (isColimitOfCreates F.op (IsLimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
preserves limits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F] :
    CreatesLimit K F.leftOp where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfCreates F (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ C`. -/
lemma preservesLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.op F.leftOp] :
    CreatesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfCreates F.leftOp (IsLimit.op hc))⟩

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ C`. -/
lemma preservesLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.op F] :
    CreatesLimit K F.rightOp where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfCreates F hc.op)⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ ⥤ D`
preserves limits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.leftOp F.rightOp] :
    CreatesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfOp (isColimitOfCreates F.rightOp (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
limits of `K : J ⥤ C`. -/
lemma preservesLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.op F] :
    CreatesLimit K F.unop where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfCreates F hc.op)⟩

/-- If `F.unop : C ⥤ D` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves
limits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F.unop] :
    CreatesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfCreates F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

/-- If `F : C ⥤ D` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesLimit K.leftOp F] :
    CreatesColimit K F.op where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfCreates F (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` preserves
colimits of `K : J ⥤ C`. -/
lemma preservesColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K.op F.op] :
    CreatesColimit K F where
  preserves {_} hc := ⟨isColimitOfOp (isLimitOfCreates F.op (IsColimit.op hc))⟩

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F] :
    CreatesColimit K F.leftOp where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfCreates F (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ C`. -/
lemma preservesColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.op F.leftOp] :
    CreatesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfCreates F.leftOp (IsColimit.op hc))⟩

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ C`. -/
lemma preservesColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.op F] :
    CreatesColimit K F.rightOp where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfCreates F hc.op)⟩

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ D`
preserves colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.leftOp F.rightOp] :
    CreatesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfOp (isLimitOfCreates F.rightOp (isLimitConeLeftOpOfCocone _ hc))⟩

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
colimits of `K : J ⥤ C`. -/
lemma preservesColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.op F] :
    CreatesColimit K F.unop where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfCreates F hc.op)⟩

/-- If `F.unop : C ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves
colimits of `K : J ⥤ Cᵒᵖ`. -/
lemma preservesColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F.unop] :
    CreatesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfCreates F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

section

variable (J)

/-- If `F : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of
shape `J`. -/
lemma preservesLimitsOfShape_op (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.op where preservesLimit {K} := preservesLimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.leftOp where preservesLimit {K} := preservesLimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.rightOp where preservesLimit {K} := preservesLimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves limits of
shape `J`. -/
lemma preservesLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.unop where preservesLimit {K} := preservesLimit_unop K F

/-- If `F : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of
shape `J`. -/
lemma preservesColimitsOfShape_op (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.op where preservesColimit {K} := preservesColimit_op K F

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.leftOp where preservesColimit {K} := preservesColimit_leftOp K F

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.rightOp where preservesColimit {K} := preservesColimit_rightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.unop where preservesColimit {K} := preservesColimit_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_of_op (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.op] :
    CreatesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.leftOp] :
    CreatesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.rightOp] :
    CreatesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits
of shape `J`. -/
lemma preservesLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.unop] :
    CreatesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_unop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ D` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_of_op (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.op] :
    CreatesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_op K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.leftOp] :
    CreatesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_leftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.rightOp] :
    CreatesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_rightOp K F

/-- If `F.unop : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits
of shape `J`. -/
lemma preservesColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.unop] :
    CreatesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_unop K F

end

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimitsOfSize_op (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits. -/
lemma preservesLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
lemma preservesLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimitsOfSize_op (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits. -/
lemma preservesColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
lemma preservesColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits. -/
lemma preservesLimitsOfSize_of_op (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F.op] :
    CreatesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.leftOp] :
    CreatesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits. -/
lemma preservesLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F.rightOp] :
    CreatesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.unop] :
    CreatesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits. -/
lemma preservesColimitsOfSize_of_op (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F.op] :
    CreatesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.leftOp] :
    CreatesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits. -/
lemma preservesColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F.rightOp] :
    CreatesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.unop] :
    CreatesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimits_op (F : C ⥤ D) [CreatesColimits F] : CreatesLimits F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves limits. -/
lemma preservesLimits_leftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimits_rightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F] : CreatesLimits F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
lemma preservesLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimits_op (F : C ⥤ D) [CreatesLimits F] : CreatesColimits F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits. -/
lemma preservesColimits_leftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimits_rightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F] :
    CreatesColimits F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
lemma preservesColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F : C ⥤ D` preserves limits. -/
lemma preservesLimits_of_op (F : C ⥤ D) [CreatesColimits F.op] : CreatesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves colimits, then `F : C ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F.leftOp] : CreatesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves colimits, then `F : Cᵒᵖ ⥤ D` preserves limits. -/
lemma preservesLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F.rightOp] :
    CreatesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
lemma preservesLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F.unop] : CreatesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F : C ⥤ D` preserves colimits. -/
lemma preservesColimits_of_op (F : C ⥤ D) [CreatesLimits F.op] : CreatesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves limits, then `F : C ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F.leftOp] :
    CreatesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves limits, then `F : Cᵒᵖ ⥤ D` preserves colimits. -/
lemma preservesColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F.rightOp] :
    CreatesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _

/-- If `F.unop : C ⥤ D` preserves limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
lemma preservesColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F.unop] : CreatesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _

/-- If `F : C ⥤ D` preserves finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
limits. -/
lemma preservesFiniteLimits_op (F : C ⥤ D) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.op where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
limits. -/
lemma preservesFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.leftOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
limits. -/
lemma preservesFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.rightOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F.unop : C ⥤ D` preserves finite
limits. -/
lemma preservesFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.unop where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_unop J F

/-- If `F : C ⥤ D` preserves finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
colimits. -/
lemma preservesFiniteColimits_op (F : C ⥤ D) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.op where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_op J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
colimits. -/
lemma preservesFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.leftOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_leftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
colimits. -/
lemma preservesFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.rightOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_rightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F.unop : C ⥤ D` preserves finite
colimits. -/
lemma preservesFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.unop where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F : C ⥤ D` preserves finite limits. -/
lemma preservesFiniteLimits_of_op (F : C ⥤ D) [CreatesFiniteColimits F.op] :
    CreatesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite colimits, then `F : C ⥤ Dᵒᵖ` preserves finite
limits. -/
lemma preservesFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F.leftOp] :
    CreatesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite colimits, then `F : Cᵒᵖ ⥤ D` preserves finite
limits. -/
lemma preservesFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F.rightOp] :
    CreatesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` preserves finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits. -/
lemma preservesFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F.unop] :
    CreatesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_unop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F : C ⥤ D` preserves finite colimits. -/
lemma preservesFiniteColimits_of_op (F : C ⥤ D) [CreatesFiniteLimits F.op] :
    CreatesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_op J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` preserves finite limits, then `F : C ⥤ Dᵒᵖ` preserves finite
colimits. -/
lemma preservesFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F.leftOp] :
    CreatesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_leftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` preserves finite limits, then `F : Cᵒᵖ ⥤ D` preserves finite
colimits. -/
lemma preservesFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F.rightOp] :
    CreatesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_rightOp J F

/-- If `F.unop : C ⥤ D` preserves finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits. -/
lemma preservesFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F.unop] :
    CreatesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_unop J F

/-- If `F : C ⥤ D` preserves finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
products. -/
lemma preservesFiniteProducts_op (F : C ⥤ D) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.op where
  preserves n := by
    apply +allowSynthFailures preservesLimitsOfShape_op
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` preserves finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
products. -/
lemma preservesFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.leftOp where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_leftOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` preserves finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
products. -/
lemma preservesFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.rightOp where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_rightOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite coproducts, then `F.unop : C ⥤ D` preserves finite
products. -/
lemma preservesFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.unop where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_unop
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` preserves finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
coproducts. -/
lemma preservesFiniteCoproducts_op (F : C ⥤ D) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.op where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_op
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` preserves finite products, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
coproducts. -/
lemma preservesFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.leftOp where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_leftOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` preserves finite products, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
coproducts. -/
lemma preservesFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.rightOp where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_rightOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite products, then `F.unop : C ⥤ D` preserves finite
coproducts. -/
lemma preservesFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.unop where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_unop
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

end CategoryTheory.Limits
