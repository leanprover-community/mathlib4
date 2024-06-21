/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# An exact functor induces a functor on derived categories

In this file, we show that if `F : C₁ ⥤ C₂` is an exact functor between
abelian categories, then there is an induced functor
`F.mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂`.

## TODO
* show that `F.mapDerivedCategory` is a triangulated functor

-/

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Limits

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

namespace CategoryTheory.Functor

/-- The functor `DerivedCategory C₁ ⥤ DerivedCategory C₂` induced
by an exact functor `F : C₁ ⥤ C₂` between abelian categories. -/
noncomputable def mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂ :=
  F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up ℤ)

/-- The functor `F.mapDerivedCategory` is induced
by `F.mapHomologicalComplex (ComplexShape.up ℤ)`. -/
noncomputable def mapDerivedCategoryFactors :
    DerivedCategory.Q ⋙ F.mapDerivedCategory ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  F.mapHomologicalComplexUpToQuasiIsoFactors _

noncomputable instance :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex _ ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactors⟩

/-- The functor `F.mapDerivedCategory` is induced
by `F.mapHomotopyCategory (ComplexShape.up ℤ)`. -/
noncomputable def mapDerivedCategoryFactorsh :
    DerivedCategory.Qh ⋙ F.mapDerivedCategory ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  F.mapHomologicalComplexUpToQuasiIsoFactorsh _

noncomputable instance :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactorsh⟩

end CategoryTheory.Functor
