/-
Copyright (c) 2025 Yaël Dillies, Moisés Herradón Cueto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Moisés Herradón Cueto
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.WithTerminal.FinCategory
import Mathlib.CategoryTheory.WithTerminal.Cone

/-!
# If a functor preserves limits, so does the induced functor in the `Over` or `Under` category

Suppose we are given categories `C` and `D`, and object `X : C`, and a functor `F : C ⥤ D`.
`F` induces a functor `Over.post F : Over X ⥤ Over (F.obj X)`. If `F` preserves limits of a
certain shape `WithTerminal J`, then `Over.post F` preserves limits of shape `J`.
As a corollary, if `F` preserves finite limits, or limits of a certain size, so does `Over.post F`.

Dually, if `F` preserves certain colimits, `Under.post F` will preserve certain colimits as well.
-/

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {X : C} {F : C ⥤ D}

-- TODO: Do we even want to keep `WidePullbackShape` around?
instance PreservesLimitsOfShape.ofWidePullbacks {J : Type*}
    [PreservesLimitsOfShape (WidePullbackShape J) F] :
    PreservesLimitsOfShape (WithTerminal <| Discrete J) F :=
  preservesLimitsOfShape_of_equiv WithTerminal.widePullbackShapeEquiv F

open WithTerminal in
instance PreservesLimitsOfShape.overPost [PreservesLimitsOfShape (WithTerminal J) F] :
    PreservesLimitsOfShape J (Over.post F (X := X)) where
  preservesLimit.preserves {coneK} isLimitConeK :=
    have isLimitConeD := (IsLimit.postcomposeHomEquiv liftFromOverComp.symm _).symm <|
      isLimitOfPreserves F (isLimitEquiv.symm isLimitConeK)
    ⟨isLimitEquiv <| isLimitConeD.ofIsoLimit <| Cones.ext (.refl _) fun | .star | .of a => by aesop⟩

instance PreservesFiniteLimits.overPost [PreservesFiniteLimits F] :
    PreservesFiniteLimits (Over.post F (X := X)) where
  preservesFiniteLimits _ := inferInstance

instance PreservesLimitsOfSize.overPost [PreservesLimitsOfSize.{w', w} F] :
    PreservesLimitsOfSize.{w', w} (Over.post F (X := X)) where

open WithInitial in
instance PreservesColimitsOfShape.underPost [PreservesColimitsOfShape (WithInitial J) F] :
    PreservesColimitsOfShape J (Under.post F (X := X)) where
  preservesColimit.preserves {coconeK} isColimitCoconeK :=
    have isColimitCoconeD := (IsColimit.precomposeHomEquiv liftFromUnderComp _).symm <|
      isColimitOfPreserves F (isColimitEquiv.symm isColimitCoconeK)
    ⟨isColimitEquiv <| isColimitCoconeD.ofIsoColimit <|
      Cocones.ext (.refl _) fun | .star | .of a => by aesop⟩

instance PreservesFiniteColimits.underPost [PreservesFiniteColimits F] :
    PreservesFiniteColimits (Under.post F (X := X)) where
  preservesFiniteColimits _ := inferInstance

instance PreservesColimitsOfSize.underPost [PreservesColimitsOfSize.{w', w} F] :
    PreservesColimitsOfSize.{w', w} (Under.post F (X := X)) where

end CategoryTheory.Limits
