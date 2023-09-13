import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.CategoryTheory.Limits.FullSubcategory

open CategoryTheory Limits ZeroObject

variable (C : Type*) [Category C] [Abelian C]
  [HasDerivedCategory C]

namespace CategoryTheory

abbrev Injectives := FullSubcategory (fun (X : C) => Injective X)

namespace Injectives

def closedUnderLimitsOfShapeDiscrete (J : Type*) :
    ClosedUnderLimitsOfShape (Discrete J) (fun (X : C) => Injective X) := by
  intro F c hc H
  have : HasLimit F := ⟨_, hc⟩
  let X := fun j => F.obj ⟨j⟩
  let e := @Discrete.natIsoFunctor _ _ _ F
  have : HasProduct X := hasLimitOfIso e
  have : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) := by
    change HasProduct X
    infer_instance
  have : ∀ j, Injective (X j) := fun j => H ⟨j⟩
  have e' : ∏ X ≅ c.pt := IsLimit.conePointUniqueUpToIso (limit.isLimit _) ((IsLimit.postcomposeHomEquiv e c).symm hc)
  exact Injective.of_iso e' inferInstance

instance : HasFiniteProducts (Injectives C) :=
  ⟨fun _ => hasLimitsOfShape_of_closed_under_limits (closedUnderLimitsOfShapeDiscrete _ _)⟩

instance : HasFiniteBiproducts (Injectives C) := HasFiniteBiproducts.of_hasFiniteProducts

instance : HasBinaryBiproducts (Injectives C) := hasBinaryBiproducts_of_finite_biproducts _

instance : HasZeroObject (Injectives C) where
  zero := by
    refine' ⟨⟨0, inferInstance⟩, _⟩
    rw [IsZero.iff_id_eq_zero]
    apply id_zero

abbrev ι : Injectives C ⥤ C := fullSubcategoryInclusion _

@[simps]
def localizerMorphism : LocalizerMorphism
  (MorphismProperty.isomorphisms (HomotopyCategory.Plus (Injectives C)))
    (HomotopyCategory.Plus.qis C) where
  functor := (ι C).mapHomotopyCategoryPlus
  map K L f (hf : IsIso f) := by
    dsimp [MorphismProperty.inverseImage, HomotopyCategory.Plus.qis]
    rw [HomotopyCategory.mem_qis_iff]
    infer_instance

/-instance : (localizerMorphism C).IsRightDerivabilityStructure := by
  let F : (HomotopyCategory.Plus C) ⥤ DerivedCategory.Plus C := sorry
  have : F.IsLocalization (HomotopyCategory.Plus.qis C) := sorry
  let G : HomotopyCategory.Plus (Injectives C) ⥤ DerivedCategory.Plus C :=
    (ι C).mapHomotopyCategoryPlus ⋙ F
  have : Full G := sorry
  have : Faithful G := sorry
  have : ∀ (X : HomotopyCategory.Plus C), IsConnected (LocalizerMorphism.RightResolution (localizerMorphism C) X) := sorry
  have : (localizerMorphism C).arrow.HasRightResolutions := sorry
  have : CatCommSq (localizerMorphism C).functor (𝟭 (HomotopyCategory.Plus (Injectives C))) F G := ⟨Iso.refl _⟩
  exact LocalizerMorphism.IsRightDerivabilityStructure.mk' (localizerMorphism C) (𝟭 _) F G-/

end Injectives

end CategoryTheory

namespace HomotopyCategory

namespace Plus


end Plus

end HomotopyCategory
