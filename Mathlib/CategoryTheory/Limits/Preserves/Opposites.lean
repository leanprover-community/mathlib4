/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limit preservation properties of `functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.leftOp` and `F.rightOp`
preserve certain (co)limits.

## Future work

* Dually, it is possible to formulate conditions about `F.op` ec. for `F` to preserve certain
(co)limits.

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

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
    preserves limits of `K : J ⥤ Cᵒᵖ`. -/
def preservesLimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.leftOp where
  preserves {_} hc :=
    isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ C`. -/
def preservesLimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F] :
    PreservesLimit K F.rightOp where
  preserves {_} hc :=
    isLimitConeRightOpOfCocone _ (isColimitOfPreserves F hc.op)

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
    limits of `K : J ⥤ C`. -/
def preservesLimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] :
    PreservesLimit K F.unop where
  preserves {_} hc :=
    isLimitConeUnopOfCocone _ (isColimitOfPreserves F hc.op)

/-- If `F : C ⥤ D` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preservesColimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.op where
  preserves {_} hc :=
    isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preservesColimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.leftOp where
  preserves {_} hc :=
    isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ C`. -/
def preservesColimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F] :
    PreservesColimit K F.rightOp where
  preserves {_} hc :=
    isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F hc.op)

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
    colimits of `K : J ⥤ C`. -/
def preservesColimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] :
    PreservesColimit K F.unop where
  preserves {_} hc :=
    isColimitCoconeUnopOfCone _ (isLimitOfPreserves F hc.op)

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

end

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

/-- If `F : C ⥤ D` preserves finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preservesFiniteLimitsOp (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.op where
  preservesFiniteLimits J (_ : SmallCategory J) _ := preservesLimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
    limits. -/
def preservesFiniteLimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.leftOp where
  preservesFiniteLimits J (_ : SmallCategory J) _ := preservesLimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preservesFiniteLimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.rightOp where
  preservesFiniteLimits J (_ : SmallCategory J) _ := preservesLimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F.unop : C ⥤ D` preserves finite
    limits. -/
def preservesFiniteLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.unop where
  preservesFiniteLimits J (_ : SmallCategory J) _ := preservesLimitsOfShapeUnop J F

/-- If `F : C ⥤ D` preserves finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preservesFiniteColimitsOp (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.op where
  preservesFiniteColimits J (_ : SmallCategory J) _ := preservesColimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` preserves finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` preserves finite
    colimits. -/
def preservesFiniteColimitsLeftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.leftOp where
  preservesFiniteColimits J (_ : SmallCategory J) _ := preservesColimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` preserves finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preservesFiniteColimitsRightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.rightOp where
  preservesFiniteColimits J (_ : SmallCategory J) _ := preservesColimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F.unop : C ⥤ D` preserves finite
    colimits. -/
def preservesFiniteColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.unop where
  preservesFiniteColimits J (_ : SmallCategory J) _ := preservesColimitsOfShapeUnop J F

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
