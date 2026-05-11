/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Triangulated derived functors using derivability structures

-/

@[expose] public section

namespace CategoryTheory

open Limits Category Pretriangulated

variable {C₁ C₂ H D₂ : Type*}
  [Category* C₁] [Category* C₂] [Category* H] [Category* D₂]
  [HasZeroObject C₁] [HasShift C₁ ℤ] [Preadditive C₁]
  [HasZeroObject C₂] [HasShift C₂ ℤ] [Preadditive C₂]
  [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [HasZeroObject D₂] [HasShift D₂ ℤ] [Preadditive D₂]
  [∀ (n : ℤ), (shiftFunctor C₁ n).Additive]
  [∀ (n : ℤ), (shiftFunctor C₂ n).Additive]
  [∀ (n : ℤ), (shiftFunctor H n).Additive]
  [∀ (n : ℤ), (shiftFunctor D₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂]
  [Pretriangulated H] [Pretriangulated D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism.Derives

variable {Φ : LocalizerMorphism W₁ W₂}
  [Φ.functor.CommShift ℤ] [Φ.functor.IsTriangulated]
  {F : C₂ ⥤ H} [F.CommShift ℤ] [F.IsTriangulated]
  (hF : Φ.Derives F)
  {L : C₂ ⥤ D₂} [L.IsLocalization W₂] [L.CommShift ℤ] [L.IsTriangulated]
  [L.mapArrow.EssSurj]

include hF in
lemma isTriangulated_of_isRightDerivedFunctor
    [Φ.IsRightDerivabilityStructure] [Φ.arrow.HasRightResolutions]
    {RF : D₂ ⥤ H} [RF.CommShift ℤ]
    (α : F ⟶ L ⋙ RF) [NatTrans.CommShift α ℤ]
    [RF.IsRightDerivedFunctor α W₂] :
    RF.IsTriangulated :=
  Functor.isTriangulated_of_leftExtension _ α (fun X Y f ↦ by
    obtain ⟨φ, ⟨eφ⟩⟩ := Functor.EssSurj.mem_essImage (F := L.mapArrow) (Arrow.mk f)
    let R : Φ.arrow.RightResolution φ := Classical.arbitrary _
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle R.X₁.hom
    exact ⟨_, Φ.functor.map_distinguished _ hT,
      hF.isIso _ _, hF.isIso _ _, hF.isIso _ _,
      ⟨(Arrow.isoMk (Localization.isoOfHom L _ _ R.hw.1)
        (Localization.isoOfHom L _ _ R.hw.2) (by simp [← Functor.map_comp])).symm ≪≫ eφ⟩⟩)

include hF in
lemma isTriangulated_of_isLeftDerivedFunctor
    [Φ.IsLeftDerivabilityStructure] [Φ.arrow.HasLeftResolutions]
    {RF : D₂ ⥤ H} [RF.CommShift ℤ]
    (α : L ⋙ RF ⟶ F) [NatTrans.CommShift α ℤ]
    [RF.IsLeftDerivedFunctor α W₂] :
    RF.IsTriangulated :=
  Functor.isTriangulated_of_rightExtension _ α (fun X Y f ↦ by
    obtain ⟨φ, ⟨eφ⟩⟩ := Functor.EssSurj.mem_essImage (F := L.mapArrow) (Arrow.mk f)
    let R : Φ.arrow.LeftResolution φ := Classical.arbitrary _
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle R.X₁.hom
    refine ⟨_, Φ.functor.map_distinguished _ hT,
      hF.isIso' _ _, hF.isIso' _ _, hF.isIso' _ _,
        ⟨?_ ≪≫ eφ⟩⟩
    exact Arrow.isoMk (Localization.isoOfHom L _ _ R.hw.1)
      (Localization.isoOfHom L _ _ R.hw.2)
      (by simp [← Functor.map_comp, dsimp% Arrow.w R.w]))

end LocalizerMorphism.Derives

end CategoryTheory
