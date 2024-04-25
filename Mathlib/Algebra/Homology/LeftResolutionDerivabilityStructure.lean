import Mathlib.Algebra.Homology.LeftResolution
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.Algebra.Homology.HomotopyCategory.Minus

open CategoryTheory Limits

namespace CochainComplex

variable {C A : Type*} [Category C] [Abelian C] [Category A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A]
  (ι : A ⥤ C) [ι.Full] [ι.Faithful] [ι.PreservesZeroMorphisms] [ι.Additive]

structure LeftResolutions where
  F : C ⥤ A
  π : F ⋙ ι ⟶ 𝟭 C
  hε (X : C) : Epi (π.app X) := by infer_instance

namespace LeftResolutions

@[simps]
def localizerMorphism :
    LocalizerMorphism ((HomotopyCategory.Minus.quasiIso C).inverseImage
      ι.mapHomotopyCategoryMinus) (HomotopyCategory.Minus.quasiIso C) where
  functor := ι.mapHomotopyCategoryMinus
  map _ _ _ hf := hf

variable (Λ : LeftResolutions ι)

/-lemma isLeftDerivabilityStructure :
    (localizerMorphism ι).op.IsRightDerivabilityStructure := by
  -- LocalizerMorphism.IsRightDerivabilityStructure.mk'
  sorry-/

end LeftResolutions

end CochainComplex
