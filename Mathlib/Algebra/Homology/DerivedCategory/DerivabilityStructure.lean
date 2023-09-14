import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.CategoryTheory.Limits.FullSubcategory

open CategoryTheory Limits ZeroObject Category

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

instance (X : Injectives C) : Injective ((ι C).obj X) := X.2
instance (X : Injectives C) : Injective X.1 := X.2

instance (K : CochainComplex (Injectives C) ℤ) (n : ℤ) :
    Injective ((((ι C).mapHomologicalComplex _).obj K).X n) := by
  dsimp
  infer_instance

instance (K : HomotopyCategory.Plus (Injectives C)) :
    CochainComplex.IsKInjective ((Functor.mapHomologicalComplex (ι C) _).obj K.obj.as) := by
  obtain ⟨n, hn⟩ := K.2
  have : CochainComplex.IsStrictlyGE
      (((ι C).mapHomotopyCategoryPlus.obj K)).obj.as n := by
    change CochainComplex.IsStrictlyGE (((ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj.as) n
    infer_instance
  apply CochainComplex.isKInjective_of_injective _ n

instance (K : HomotopyCategory.Plus (Injectives C)) :
    CochainComplex.IsKInjective ((Functor.mapHomotopyCategoryPlus (ι C)).obj K).obj.as := by
  change CochainComplex.IsKInjective ((Functor.mapHomologicalComplex (ι C) _).obj K.obj.as)
  infer_instance

lemma Qh_map_bijective_ι_mapHomotopyCategoryPlus
    (K : HomotopyCategory.Plus C) (L : HomotopyCategory.Plus (Injectives C)) :
    Function.Bijective (DerivedCategory.Plus.Qh.map : (K ⟶ ((ι C).mapHomotopyCategoryPlus).obj L) → _):= by
  apply DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
  infer_instance

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

noncomputable instance : ReflectsIsomorphisms (((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)) :=
  reflectsIsomorphisms_of_full_and_faithful _

-- TODO: show it follows from [EnoughInjectives C]
variable [(localizerMorphism C).HasRightResolutions]

variable {C}

lemma localizerMorphism_lift_map_on_resolutions {X Y : HomotopyCategory.Plus C} (φ : X ⟶ Y)
    (X' : (localizerMorphism C).RightResolution X) (Y' : (localizerMorphism C).RightResolution Y) :
    ∃ (ψ : X'.X₁ ⟶ Y'.X₁), X'.w ≫ (localizerMorphism C).functor.map ψ = φ ≫ Y'.w := by
  let F := ((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
  have := DerivedCategory.Plus.Qh_inverts C _ X'.hw
  obtain ⟨γ, hγ⟩ := F.map_surjective (inv (DerivedCategory.Plus.Qh.map X'.w) ≫ DerivedCategory.Plus.Qh.map φ ≫ DerivedCategory.Plus.Qh.map Y'.w)
  refine' ⟨γ, (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective _ _ _).1 _⟩
  · dsimp [localizerMorphism]
    infer_instance
  · dsimp
    erw [Functor.map_comp, hγ, Functor.map_comp, IsIso.hom_inv_id_assoc]

instance : (localizerMorphism C).arrow.HasRightResolutions := fun f => by
  have X : (localizerMorphism C).RightResolution f.left := Classical.arbitrary _
  have Y : (localizerMorphism C).RightResolution f.right := Classical.arbitrary _
  obtain ⟨φ, hφ⟩ := localizerMorphism_lift_map_on_resolutions f.hom X Y
  exact
   ⟨{ X₁ := Arrow.mk φ
      w  :=
        { left := X.w
          right := Y.w
          w := hφ }
      hw := ⟨X.hw, Y.hw⟩ }⟩

instance  (X : HomotopyCategory.Plus C) :
    IsConnected (LocalizerMorphism.RightResolution (localizerMorphism C) X) :=
  zigzag_isConnected (fun Y Z => by
    obtain ⟨φ, hφ⟩ := localizerMorphism_lift_map_on_resolutions (𝟙 X) Y Z
    rw [id_comp] at hφ
    have : IsIso ((((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).map φ) := by
      replace hφ := DerivedCategory.Plus.Qh.congr_map hφ
      dsimp at hφ
      rw [Functor.map_comp] at hφ
      have := DerivedCategory.Plus.Qh_inverts C Y.w Y.hw
      have := DerivedCategory.Plus.Qh_inverts C Z.w Z.hw
      exact IsIso.of_isIso_fac_left hφ
    have hφ' : IsIso φ := isIso_of_reflects_iso φ
      ((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    exact Relation.ReflTransGen.single
      (Or.inl ⟨LocalizerMorphism.RightResolution.Hom.mk φ hφ' hφ⟩))

/-instance [EnoughInjectives C] : (localizerMorphism C).IsRightDerivabilityStructure := by
  have : DerivedCategory.Plus.Qh.IsLocalization (HomotopyCategory.Plus.qis C) := sorry
  exact LocalizerMorphism.IsRightDerivabilityStructure.mk' (localizerMorphism C) (𝟭 _)
    DerivedCategory.Plus.Qh ((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)-/

end Injectives

end CategoryTheory
