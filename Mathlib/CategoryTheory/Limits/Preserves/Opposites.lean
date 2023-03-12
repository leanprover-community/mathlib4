/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.preserves.opposites
! leanprover-community/mathlib commit 9ed4366659f4fcca0ee70310d26ac5518dcb6dd0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Opposites
import Mathbin.CategoryTheory.Limits.Preserves.Finite

/-!
# Limit preservation properties of `functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.left_op` and `F.right_op`
preserve certain (co)limits.

## Future work

* Dually, it is possible to formulate conditions about `F.op` ec. for `F` to preserve certain
(co)limits.

-/


universe w w' v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J]

/-- If `F : C ⥤ D` preserves colimits of `K.left_op : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ Cᵒᵖ`. -/
def preservesLimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F] : PreservesLimit K F.op
    where preserves c hc :=
    isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))
#align category_theory.limits.preserves_limit_op CategoryTheory.Limits.preservesLimitOp

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of `K.left_op : Jᵒᵖ ⥤ C`, then `F.left_op : Cᵒᵖ ⥤ D`
    preserves limits of `K : J ⥤ Cᵒᵖ`. -/
def preservesLimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.leftOp
    where preserves c hc :=
    isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))
#align category_theory.limits.preserves_limit_left_op CategoryTheory.Limits.preservesLimitLeftOp

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.right_op : C ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ C`. -/
def preservesLimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F] :
    PreservesLimit K F.rightOp
    where preserves c hc :=
    isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitConeOp _ hc))
#align category_theory.limits.preserves_limit_right_op CategoryTheory.Limits.preservesLimitRightOp

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
    limits of `K : J ⥤ C`. -/
def preservesLimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] :
    PreservesLimit K F.unop
    where preserves c hc :=
    isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitConeOp _ hc))
#align category_theory.limits.preserves_limit_unop CategoryTheory.Limits.preservesLimitUnop

/-- If `F : C ⥤ D` preserves limits of `K.left_op : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preservesColimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.op
    where preserves c hc :=
    isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))
#align category_theory.limits.preserves_colimit_op CategoryTheory.Limits.preservesColimitOp

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of `K.left_op : Jᵒᵖ ⥤ C`, then `F.left_op : Cᵒᵖ ⥤ D` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preservesColimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.leftOp
    where preserves c hc :=
    isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))
#align category_theory.limits.preserves_colimit_left_op CategoryTheory.Limits.preservesColimitLeftOp

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.right_op : C ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ C`. -/
def preservesColimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F] :
    PreservesColimit K F.rightOp
    where preserves c hc :=
    isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitCoconeOp _ hc))
#align category_theory.limits.preserves_colimit_right_op CategoryTheory.Limits.preservesColimitRightOp

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
    colimits of `K : J ⥤ C`. -/
def preservesColimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] :
    PreservesColimit K F.unop
    where preserves c hc :=
    isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitCoconeOp _ hc))
#align category_theory.limits.preserves_colimit_unop CategoryTheory.Limits.preservesColimitUnop

section

variable (J)

/-- If `F : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of
    shape `J`. -/
def preservesLimitsOfShapeOp (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.op where PreservesLimit K := preservesLimitOp K F
#align category_theory.limits.preserves_limits_of_shape_op CategoryTheory.Limits.preservesLimitsOfShapeOp

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.left_op : Cᵒᵖ ⥤ D` preserves limits
    of shape `J`. -/
def preservesLimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.leftOp where PreservesLimit K := preservesLimitLeftOp K F
#align category_theory.limits.preserves_limits_of_shape_left_op CategoryTheory.Limits.preservesLimitsOfShapeLeftOp

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.right_op : C ⥤ Dᵒᵖ` preserves limits
    of shape `J`. -/
def preservesLimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.rightOp where PreservesLimit K := preservesLimitRightOp K F
#align category_theory.limits.preserves_limits_of_shape_right_op CategoryTheory.Limits.preservesLimitsOfShapeRightOp

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves limits of
    shape `J`. -/
def preservesLimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.unop where PreservesLimit K := preservesLimitUnop K F
#align category_theory.limits.preserves_limits_of_shape_unop CategoryTheory.Limits.preservesLimitsOfShapeUnop

/-- If `F : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of
    shape `J`. -/
def preservesColimitsOfShapeOp (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.op where PreservesColimit K := preservesColimitOp K F
#align category_theory.limits.preserves_colimits_of_shape_op CategoryTheory.Limits.preservesColimitsOfShapeOp

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.left_op : Cᵒᵖ ⥤ D` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.leftOp where PreservesColimit K := preservesColimitLeftOp K F
#align category_theory.limits.preserves_colimits_of_shape_left_op CategoryTheory.Limits.preservesColimitsOfShapeLeftOp

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.right_op : C ⥤ Dᵒᵖ` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.rightOp where PreservesColimit K := preservesColimitRightOp K F
#align category_theory.limits.preserves_colimits_of_shape_right_op CategoryTheory.Limits.preservesColimitsOfShapeRightOp

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves colimits
    of shape `J`. -/
def preservesColimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.unop where PreservesColimit K := preservesColimitUnop K F
#align category_theory.limits.preserves_colimits_of_shape_unop CategoryTheory.Limits.preservesColimitsOfShapeUnop

end

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsOp (F : C ⥤ D) [PreservesColimits F] : PreservesLimits F.op
    where PreservesLimitsOfShape J _ := preserves_limits_of_shape_op J F
#align category_theory.limits.preserves_limits_op CategoryTheory.Limits.preservesLimitsOp

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.left_op : Cᵒᵖ ⥤ D` preserves limits. -/
def preservesLimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.leftOp
    where PreservesLimitsOfShape J _ := preserves_limits_of_shape_left_op J F
#align category_theory.limits.preserves_limits_left_op CategoryTheory.Limits.preservesLimitsLeftOp

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.right_op : C ⥤ Dᵒᵖ` preserves limits. -/
def preservesLimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F] : PreservesLimits F.rightOp
    where PreservesLimitsOfShape J _ := preserves_limits_of_shape_right_op J F
#align category_theory.limits.preserves_limits_right_op CategoryTheory.Limits.preservesLimitsRightOp

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
def preservesLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.unop
    where PreservesLimitsOfShape J _ := preserves_limits_of_shape_unop J F
#align category_theory.limits.preserves_limits_unop CategoryTheory.Limits.preservesLimitsUnop

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
def perservesColimitsOp (F : C ⥤ D) [PreservesLimits F] : PreservesColimits F.op
    where PreservesColimitsOfShape J _ := preserves_colimits_of_shape_op J F
#align category_theory.limits.perserves_colimits_op CategoryTheory.Limits.perservesColimitsOp

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.left_op : Cᵒᵖ ⥤ D` preserves colimits. -/
def preservesColimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.leftOp
    where PreservesColimitsOfShape J _ := preserves_colimits_of_shape_left_op J F
#align category_theory.limits.preserves_colimits_left_op CategoryTheory.Limits.preservesColimitsLeftOp

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.right_op : C ⥤ Dᵒᵖ` preserves colimits. -/
def preservesColimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F] : PreservesColimits F.rightOp
    where PreservesColimitsOfShape J _ := preserves_colimits_of_shape_right_op J F
#align category_theory.limits.preserves_colimits_right_op CategoryTheory.Limits.preservesColimitsRightOp

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
def preservesColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.unop
    where PreservesColimitsOfShape J _ := preserves_colimits_of_shape_unop J F
#align category_theory.limits.preserves_colimits_unop CategoryTheory.Limits.preservesColimitsUnop

end

section

-- Preservation of finite (colimits) is only defined when the morphisms of C and D live in the same
-- universe.
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]

/-- If `F : C ⥤ D` preserves finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preservesFiniteLimitsOp (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteLimits F.op
    where PreservesFiniteLimits J _ _ := preserves_limits_of_shape_op J F
#align category_theory.limits.preserves_finite_limits_op CategoryTheory.Limits.preservesFiniteLimitsOp

/-- If `F : C ⥤ Dᵒᵖ` preserves finite colimits, then `F.left_op : Cᵒᵖ ⥤ D` preserves finite
    limits. -/
def preservesFiniteLimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.leftOp
    where PreservesFiniteLimits J _ _ := preserves_limits_of_shape_left_op J F
#align category_theory.limits.preserves_finite_limits_left_op CategoryTheory.Limits.preservesFiniteLimitsLeftOp

/-- If `F : Cᵒᵖ ⥤ D` preserves finite colimits, then `F.right_op : C ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preservesFiniteLimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.rightOp
    where PreservesFiniteLimits J _ _ := preserves_limits_of_shape_right_op J F
#align category_theory.limits.preserves_finite_limits_right_op CategoryTheory.Limits.preservesFiniteLimitsRightOp

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F.unop : C ⥤ D` preserves finite
    limits. -/
def preservesFiniteLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.unop
    where PreservesFiniteLimits J _ _ := preserves_limits_of_shape_unop J F
#align category_theory.limits.preserves_finite_limits_unop CategoryTheory.Limits.preservesFiniteLimitsUnop

/-- If `F : C ⥤ D` preserves finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preservesFiniteColimitsOp (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteColimits F.op
    where PreservesFiniteColimits J _ _ := preserves_colimits_of_shape_op J F
#align category_theory.limits.preserves_finite_colimits_op CategoryTheory.Limits.preservesFiniteColimitsOp

/-- If `F : C ⥤ Dᵒᵖ` preserves finite limits, then `F.left_op : Cᵒᵖ ⥤ D` preserves finite
    colimits. -/
def preservesFiniteColimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.leftOp
    where PreservesFiniteColimits J _ _ := preserves_colimits_of_shape_left_op J F
#align category_theory.limits.preserves_finite_colimits_left_op CategoryTheory.Limits.preservesFiniteColimitsLeftOp

/-- If `F : Cᵒᵖ ⥤ D` preserves finite limits, then `F.right_op : C ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preservesFiniteColimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.rightOp
    where PreservesFiniteColimits J _ _ := preserves_colimits_of_shape_right_op J F
#align category_theory.limits.preserves_finite_colimits_right_op CategoryTheory.Limits.preservesFiniteColimitsRightOp

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F.unop : C ⥤ D` preserves finite
    colimits. -/
def preservesFiniteColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.unop
    where PreservesFiniteColimits J _ _ := preserves_colimits_of_shape_unop J F
#align category_theory.limits.preserves_finite_colimits_unop CategoryTheory.Limits.preservesFiniteColimitsUnop

end

end CategoryTheory.Limits

