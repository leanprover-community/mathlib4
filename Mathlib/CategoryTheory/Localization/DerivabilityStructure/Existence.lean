import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Pointwise
import Mathlib.CategoryTheory.Functor.Derived.Pointwise

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₄} D₁] [Category.{v₅} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) [Φ.IsRightDerivabilityStructure]
  (F : C₂ ⥤ H) (hF : W₁.IsInvertedBy (Φ.functor ⋙ F))

lemma hasPointwiseRightDerivedFunctor : F.HasPointwiseRightDerivedFunctor W₂ := by
  rw [Φ.hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure F]
  exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _ hF

lemma hasRightDerivedFunctor : F.HasRightDerivedFunctor W₂ := by
  have := Φ.hasPointwiseRightDerivedFunctor F hF
  infer_instance

variable (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂] (RF : D₂ ⥤ H) (α : F ⟶ L₂ ⋙ RF)
  [RF.IsRightDerivedFunctor α W₂]

lemma isIso_app_of_isRightDerivedFunctor (X : C₁) : IsIso (α.app (Φ.functor.obj X)) := by
  have := Functor.hasPointwiseRightDerivedFunctor_of_inverts _ hF
  rw [← isIso_α_iff_of_isRightDerivabilityStructure Φ W₁.Q L₂ F (Localization.lift _ hF W₁.Q)
    (Localization.fac _ hF W₁.Q).inv RF α]
  infer_instance

end LocalizerMorphism

end CategoryTheory
