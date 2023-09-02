import Mathlib.CategoryTheory.Localization.Resolution
import Mathlib.CategoryTheory.GuitartExact

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

class IsRightDerivabilityStructure extends Φ.HasRightResolutions where
  guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom

-- TODO: show `guitartExact'` does not depend on the choice of the localizations

end LocalizerMorphism

end CategoryTheory
