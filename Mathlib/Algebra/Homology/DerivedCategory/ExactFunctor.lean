/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# An exact functor induces a functor on derived categories

In this file, we show that if `F : C₁ ⥤ C₂` is an exact functor between
abelian categories, then there is an induced triangulated functor
`F.mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂`.

-/

assert_not_exists TwoSidedIdeal

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Category Limits

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

lemma mapDerivedCategoryFactorsh_hom_app (K : CochainComplex C₁ ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
        (DerivedCategory.quotientCompQhIso C₂).inv.app _ ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) :=
  F.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app K

noncomputable instance :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactorsh⟩

noncomputable instance : F.mapDerivedCategory.CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) ℤ
    (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory

instance : NatTrans.CommShift F.mapDerivedCategoryFactorsh.hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso
      DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
        (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
          F.mapDerivedCategory).hom ℤ)

instance : NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ :=
  NatTrans.CommShift.verticalComposition (DerivedCategory.quotientCompQhIso C₁).inv
    (DerivedCategory.quotientCompQhIso C₂).hom
    (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
    F.mapDerivedCategoryFactorsh.hom F.mapDerivedCategoryFactors.hom ℤ (by
      ext K
      dsimp
      simp only [id_comp, mapDerivedCategoryFactorsh_hom_app, assoc, comp_id,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_app, map_id, comp_obj])

instance : F.mapDerivedCategory.IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso F.mapDerivedCategoryFactorsh

end CategoryTheory.Functor
