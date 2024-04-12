import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Existence
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
import Mathlib.CategoryTheory.Triangulated.Functor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Category Limits Pretriangulated

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₄} D₁] [Category.{v₅} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) [Φ.IsRightDerivabilityStructure]
  [Φ.arrow.HasRightResolutions]
  (F : C₂ ⥤ H) (hF : W₁.IsInvertedBy (Φ.functor ⋙ F))
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂] [L₂.mapArrow.EssSurj]
  (RF : D₂ ⥤ H) (α : F ⟶ L₂ ⋙ RF) [RF.IsRightDerivedFunctor α W₂]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₂ ℤ] [HasShift H ℤ]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D₂] [HasZeroObject H]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D₂] [Preadditive H]
  [∀ (n : ℤ), (shiftFunctor C₁ n).Additive] [∀ (n : ℤ), (shiftFunctor C₂ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D₂ n).Additive] [∀ (n : ℤ), (shiftFunctor H n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂] [Pretriangulated D₂] [Pretriangulated H]
  [F.CommShift ℤ] [L₂.CommShift ℤ] [RF.CommShift ℤ] [Φ.functor.CommShift ℤ]
  [NatTrans.CommShift α ℤ] [F.IsTriangulated] [L₂.IsTriangulated] [Φ.functor.IsTriangulated]

lemma isTriangulated_of_isRightDerivedFunctor : RF.IsTriangulated :=
  RF.isTriangulated_of_isRightDerivedFunctor α (fun X Y f => by
    have φ : Φ.arrow.RightResolution (L₂.mapArrow.objPreimage (Arrow.mk f)) :=
      Classical.arbitrary _
    obtain ⟨Z, a, b, hT⟩ := distinguished_cocone_triangle φ.X₁.hom
    refine' ⟨_, Φ.functor.map_distinguished _ hT,
      Φ.isIso_app_of_isRightDerivedFunctor F hF L₂ RF α _,
      Φ.isIso_app_of_isRightDerivedFunctor F hF L₂ RF α _,
      Φ.isIso_app_of_isRightDerivedFunctor F hF L₂ RF α _,
      ⟨Iso.symm _ ≪≫ L₂.mapArrow.objObjPreimageIso (Arrow.mk f)⟩⟩
    refine' Arrow.isoMk (Localization.isoOfHom L₂ W₂ _ φ.hw.left)
      (Localization.isoOfHom L₂ W₂ _ φ.hw.right) _
    dsimp
    simp only [← L₂.map_comp, Arrow.w_mk_right])

end LocalizerMorphism

end CategoryTheory
