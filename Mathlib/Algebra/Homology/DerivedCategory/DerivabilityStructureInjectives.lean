import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Existence
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Homology.Factorizations.CM5a

open CategoryTheory Limits ZeroObject Category

variable (C D : Type*) [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {H : Type*} [Category H]

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

instance (X : Injectives C) : Injective ((ι C).obj X) := X.2

instance (X : HomotopyCategory.Plus (Injectives C)) (n : ℤ) :
    Injective (((ι C).mapHomotopyCategoryPlus.obj X).obj.as.X n) := by
  change Injective ((ι C).obj (X.obj.as.X n))
  infer_instance

variable {C}

def liftHomotopyCategoryPlusOfInjective (K : HomotopyCategory.Plus C)
  [∀ (n : ℤ), Injective (K.obj.as.X n)] : HomotopyCategory.Plus (Injectives C) :=
    { obj :=
       ⟨{ X := fun n => ⟨K.obj.as.X n, inferInstance⟩
          d := fun i j => K.obj.as.d i j
          shape := fun i j hij => K.obj.as.shape i j hij
          d_comp_d' := fun i j hij => K.obj.as.d_comp_d' i j hij }⟩
      property := by
        obtain ⟨n, hn⟩ := K.2
        refine' ⟨n, ⟨fun i hi => _⟩⟩
        simpa only [IsZero.iff_id_eq_zero] using
          CochainComplex.isZero_of_isStrictlyGE K.obj.as n i hi }

def isoMapHomotopyCategoryPlusιObj (K : HomotopyCategory.Plus C)
    [∀ (n : ℤ), Injective (K.obj.as.X n)] :
    (ι C).mapHomotopyCategoryPlus.obj (liftHomotopyCategoryPlusOfInjective K) ≅ K := Iso.refl _

lemma mem_essImage_mapHomotopyCategoryPlus_ι_of_injective (K : HomotopyCategory.Plus C)
    [∀ (n : ℤ), Injective (K.obj.as.X n)] :
    K ∈ (ι C).mapHomotopyCategoryPlus.essImage :=
  ⟨_, ⟨isoMapHomotopyCategoryPlusιObj K⟩⟩

variable (C)

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

variable {C}

noncomputable def rightResolution_localizerMorphism (K : CochainComplex C ℤ) (n : ℤ) [hK : K.IsStrictlyGE n] [EnoughInjectives C] :
    (localizerMorphism C).RightResolution (⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, n, hK⟩) where
  X₁ := liftHomotopyCategoryPlusOfInjective ⟨⟨K.injectiveResolution n⟩, ⟨n, inferInstance⟩⟩
  w := (HomotopyCategory.quotient _ _).map (K.ιInjectiveResolution n)
  hw := by
    dsimp [HomotopyCategory.Plus.qis, MorphismProperty.inverseImage, HomotopyCategory.Plus.ι, Triangulated.Subcategory.ι]
    rw [HomotopyCategory.quotient_map_mem_qis_iff, HomologicalComplex.qis_iff]
    infer_instance

instance [EnoughInjectives C] : (Injectives.localizerMorphism C).HasRightResolutions := by
  rintro ⟨⟨K⟩, n, hn⟩
  exact ⟨rightResolution_localizerMorphism K n⟩

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

instance [EnoughInjectives C] : (localizerMorphism C).arrow.HasRightResolutions := fun f => by
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

instance [EnoughInjectives C] (X : HomotopyCategory.Plus C) :
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

/-- The inclusion functor from the homotopy category `K^+` of injective objects
into the homotopy category `K^+` induces a right derivability structure, which allow
to derive any functor from `K^+`. -/
instance [EnoughInjectives C] : (localizerMorphism C).IsRightDerivabilityStructure :=
  LocalizerMorphism.IsRightDerivabilityStructure.mk' (localizerMorphism C) (𝟭 _)
    DerivedCategory.Plus.Qh ((ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)

section

variable [EnoughInjectives C] (F : HomotopyCategory.Plus C ⥤ H)

/-- Any functor the homotopy category `K^+` has a right derived functor with respect
to quasi-isomorphisms.  -/
instance : F.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.qis C) :=
  (localizerMorphism C).hasPointwiseRightDerivedFunctor F
    (MorphismProperty.isomorphisms_isInvertedBy _)

variable (F' : DerivedCategory.Plus C ⥤ H) (α : F ⟶ DerivedCategory.Plus.Qh ⋙ F')
  [F'.IsRightDerivedFunctor α (HomotopyCategory.Plus.qis C)]

instance (K : HomotopyCategory.Plus C) [(∀ (n : ℤ), Injective (K.obj.as.X n))] : IsIso (α.app K) := by
  have : ∀ (Y : HomotopyCategory.Plus (Injectives C)),
      IsIso (α.app ((ι C).mapHomotopyCategoryPlus.obj Y)) := fun Y =>
    (localizerMorphism C).isIso_app_of_isRightDerivedFunctor _
      (MorphismProperty.isomorphisms_isInvertedBy _) _ _ _ _
  obtain ⟨Y, ⟨e⟩⟩ := mem_essImage_mapHomotopyCategoryPlus_ι_of_injective K
  rw [← NatTrans.isIso_app_iff_of_iso α e]
  infer_instance

example (X : HomotopyCategory.Plus (Injectives C)) :
    IsIso ((F.totalRightDerivedUnit DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.qis C)).app ((ι C).mapHomotopyCategoryPlus.obj X)) := by
  infer_instance

end

end Injectives

namespace Functor

variable {C D}
variable (F : C ⥤ D) [F.Additive]

section

variable [EnoughInjectives C]

noncomputable def rightDerivedFunctorPlus :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.qis C)

noncomputable def rightDerivedFunctorPlusUnit :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus :=
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.qis C)

instance :
    F.rightDerivedFunctorPlus.IsRightDerivedFunctor
      F.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.qis C) := by
  dsimp only [rightDerivedFunctorPlus, rightDerivedFunctorPlusUnit]
  infer_instance

instance (X : HomotopyCategory.Plus (Injectives C)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((Injectives.ι C).mapHomotopyCategoryPlus.obj X)) := by
  dsimp only [rightDerivedFunctorPlus, rightDerivedFunctorPlusUnit]
  infer_instance

noncomputable def rightDerived' (n : ℕ) : C ⥤ D :=
  DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor D n

end

end Functor

end CategoryTheory
