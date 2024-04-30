import Mathlib.Algebra.Homology.LeftResolution
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.Algebra.Homology.DerivedCategory.Minus

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

lemma isLocalization [HasDerivedCategory C] :
    (ι.mapHomotopyCategoryMinus ⋙ DerivedCategory.Minus.Qh).IsLocalization (quasiIso ι) := by
  have := Λ.localizerMorphism_isLocalizedEquivalence
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization (localizerMorphism ι)
    (DerivedCategory.Minus.Qh )

lemma isLeftDerivabilityStructure :
    (localizerMorphism ι).op.IsRightDerivabilityStructure := by
  have : HasDerivedCategory C := HasDerivedCategory.standard _
  have : ((Functor.mapHomotopyCategoryMinus ι).op ⋙ DerivedCategory.Minus.Qh.op).IsLocalization
      (quasiIso ι).op := (Functor.isLocalization_iff_op _ _).1 Λ.isLocalization
  have : ∀ (X₂ : (HomotopyCategory.Minus C)ᵒᵖ),
    IsConnected (LocalizerMorphism.RightResolution (LocalizerMorphism.op (localizerMorphism ι)) X₂) := sorry
  have : LocalizerMorphism.HasRightResolutions (LocalizerMorphism.arrow (LocalizerMorphism.op (localizerMorphism ι))) := sorry
  have : CatCommSq (LocalizerMorphism.op (localizerMorphism ι)).functor
    ((Functor.mapHomotopyCategoryMinus ι).op ⋙ DerivedCategory.Minus.Qh.op) DerivedCategory.Minus.Qh.op
    (𝟭 (DerivedCategory.Minus C)ᵒᵖ) := ⟨Iso.refl _⟩
  exact LocalizerMorphism.IsRightDerivabilityStructure.mk' (localizerMorphism ι).op
    (ι.mapHomotopyCategoryMinus.op ⋙ (DerivedCategory.Minus.Qh (C := C)).op)
    DerivedCategory.Minus.Qh.op (F := 𝟭 _)-/

end LeftResolutions

end CochainComplex
