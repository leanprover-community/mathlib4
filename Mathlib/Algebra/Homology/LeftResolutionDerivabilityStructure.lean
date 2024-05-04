import Mathlib.Algebra.Homology.LeftResolution
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.Algebra.Homology.DerivedCategory.Minus

open CategoryTheory Limits

namespace CochainComplex

variable {C A : Type*} [Category C] [Abelian C] [Category A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A]
  (ι : A ⥤ C) [ι.Full] [ι.Faithful] [ι.PreservesZeroMorphisms] [ι.Additive]

namespace LeftResolutions

abbrev quasiIso : MorphismProperty (HomotopyCategory.Minus A) :=
  (HomotopyCategory.Minus.quasiIso C).inverseImage ι.mapHomotopyCategoryMinus

@[simps]
def localizerMorphism :
    LocalizerMorphism (quasiIso ι) (HomotopyCategory.Minus.quasiIso C) where
  functor := ι.mapHomotopyCategoryMinus
  map _ _ _ hf := hf

variable {ι}
variable (Λ : LeftResolutions ι)

/-lemma localizerMorphism_isLocalizedEquivalence :
    (localizerMorphism ι).IsLocalizedEquivalence := by
  have := Λ
  sorry

lemma localizerMorphism_op_isLocalizedEquivalence :
    (localizerMorphism ι).op.IsLocalizedEquivalence := by
  have := Λ
  sorry

lemma isLocalization [HasDerivedCategory C] :
    (ι.mapHomotopyCategoryMinus ⋙ DerivedCategory.Minus.Qh).IsLocalization (quasiIso ι) := by
  have := Λ.localizerMorphism_isLocalizedEquivalence
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization (localizerMorphism ι)
    (DerivedCategory.Minus.Qh )

lemma isLeftDerivabilityStructure :
    (localizerMorphism ι).op.IsRightDerivabilityStructure := by
  have paf := Λ.localizerMorphism_op_isLocalizedEquivalence
  have : ∀ (X₂ : (HomotopyCategory.Minus C)ᵒᵖ),
    IsConnected (LocalizerMorphism.RightResolution (LocalizerMorphism.op (localizerMorphism ι)) X₂) := sorry
  have : LocalizerMorphism.HasRightResolutions (LocalizerMorphism.arrow (LocalizerMorphism.op (localizerMorphism ι))) := sorry
  apply LocalizerMorphism.IsRightDerivabilityStructure.mk'-/

end LeftResolutions

end CochainComplex
