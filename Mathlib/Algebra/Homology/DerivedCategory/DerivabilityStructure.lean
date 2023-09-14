import Mathlib.Algebra.Homology.DerivedCategory.Plus
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

noncomputable instance : CatCommSq (localizerMorphism C).functor
    (𝟭 (HomotopyCategory.Plus (Injectives C)))
    DerivedCategory.Plus.Qh ((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) :=
  ⟨Iso.refl _⟩

variable {C}

instance (K : HomotopyCategory.Plus (Injectives C)) (n : ℤ) :
    Injective (((ι C).mapHomotopyCategoryPlus.obj K).obj.as.X n) :=
  (K.1.as.X n).2

lemma Qh_map_bijective_ι_mapHomotopyCategoryPlus
    (K : HomotopyCategory.Plus C) (L : HomotopyCategory.Plus (Injectives C)) :
    Function.Bijective (DerivedCategory.Plus.Qh.map : (K ⟶ ((ι C).mapHomotopyCategoryPlus).obj L) → _):= by
  apply DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
  obtain ⟨n, hn⟩ := L.2
  have : CochainComplex.IsStrictlyGE
      (((ι C).mapHomotopyCategoryPlus.obj L)).obj.as n := by
    change CochainComplex.IsStrictlyGE (((ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj.as) n
    infer_instance
  apply CochainComplex.isKInjective_of_injective _ n

variable (C)

noncomputable instance : Full (((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)) :=
  Functor.fullOfSurjective _ (fun K L f => by
    obtain ⟨g, rfl⟩ := (Qh_map_bijective_ι_mapHomotopyCategoryPlus (((ι C).mapHomotopyCategoryPlus).obj K) L).2 f
    obtain ⟨h, rfl⟩ := ((ι C).mapHomotopyCategoryPlus).map_surjective g
    exact ⟨h, rfl⟩)

noncomputable instance : Faithful (((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)) where
  map_injective {K L} f₁ f₂ hf := by
    apply ((ι C).mapHomotopyCategoryPlus).map_injective
    exact ((Qh_map_bijective_ι_mapHomotopyCategoryPlus
      (((ι C).mapHomotopyCategoryPlus).obj K) L).1 hf)

/-instance [EnoughInjectives C] : (localizerMorphism C).IsRightDerivabilityStructure := by
  have : DerivedCategory.Plus.Qh.IsLocalization (HomotopyCategory.Plus.qis C) := sorry
  have : ∀ (X : HomotopyCategory.Plus C), IsConnected (LocalizerMorphism.RightResolution (localizerMorphism C) X) := sorry
  have : (localizerMorphism C).arrow.HasRightResolutions := sorry
  exact LocalizerMorphism.IsRightDerivabilityStructure.mk' (localizerMorphism C) (𝟭 _) DerivedCategory.Plus.Qh ((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)-/

end Injectives

end CategoryTheory

namespace HomotopyCategory

namespace Plus


end Plus

end HomotopyCategory
