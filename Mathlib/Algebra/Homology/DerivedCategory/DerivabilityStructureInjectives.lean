/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyFiber
public import Mathlib.Algebra.Homology.ModelCategory.Injective
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
public import Mathlib.CategoryTheory.GuitartExact.Quotient
public import Mathlib.CategoryTheory.ObjectProperty.HomologicalComplex
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# The projective derivability structure

-/

@[expose] public section

universe w₁ w₂

open HomotopicalAlgebra CategoryTheory Limits ZeroObject Category

variable (C : Type*) [Category C] [Abelian C]
  {H : Type*} [Category H]

namespace CategoryTheory

abbrev InjectiveObject := ObjectProperty.FullSubcategory (fun (X : C) => Injective X)

namespace InjectiveObject

instance closedUnderLimitsOfShapeDiscrete (J : Type*) :
    ObjectProperty.IsClosedUnderLimitsOfShape (fun (X : C) => Injective X) (Discrete J) where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    have : HasLimit p.diag := ⟨_, p.isLimit⟩
    let X := fun j => p.diag.obj ⟨j⟩
    let e := Discrete.natIsoFunctor (F := p.diag)
    have : HasProduct X := hasLimit_of_iso e
    have : HasLimit (Discrete.functor (p.diag.obj ∘ Discrete.mk)) := by
      change HasProduct X
      infer_instance
    have : ∀ j, Injective (X j) := fun j => p.prop_diag_obj ⟨j⟩
    have e' : ∏ᶜ X ≅ Y := IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      ((IsLimit.postcomposeHomEquiv e _).symm p.isLimit)
    exact Injective.of_iso e' inferInstance

instance : HasFiniteProducts (InjectiveObject C) where
  out n := by infer_instance

instance : HasFiniteBiproducts (InjectiveObject C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance : HasBinaryBiproducts (InjectiveObject C) := hasBinaryBiproducts_of_finite_biproducts _

instance : HasZeroObject (InjectiveObject C) where
  zero := by
    refine ⟨⟨0, inferInstance⟩, ?_⟩
    rw [IsZero.iff_id_eq_zero]
    ext : 1
    apply id_zero

abbrev ι : InjectiveObject C ⥤ C := ObjectProperty.ι _

instance (X : InjectiveObject C) : Injective ((ι C).obj X) := X.2

instance (X : InjectiveObject C) : Injective X.obj := X.2

instance (X : HomotopyCategory.Plus (InjectiveObject C)) (n : ℤ) :
    Injective (((ι C).mapHomotopyCategoryPlus.obj X).obj.as.X n) := by
  change Injective ((ι C).obj (X.obj.as.X n))
  infer_instance

instance (K : CochainComplex.Plus (InjectiveObject C)) :
    CochainComplex.IsKInjective
      (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K.obj) := by
  obtain ⟨K, n, hn⟩ := K
  let L := ((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K
  have (n : ℤ) : Injective (L.X n) := by dsimp [L]; infer_instance
  exact CochainComplex.isKInjective_of_injective L n

end InjectiveObject

end CategoryTheory

namespace CochainComplex.Plus

variable {C}

lemma exists_injective_resolution [EnoughInjectives C]
    (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsStrictlyGE n] :
    ∃ (L : CochainComplex.Plus (InjectiveObject C)) (_ : L.obj.IsStrictlyGE n)
      (i : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L),
        quasiIso C i := by
  obtain ⟨L, i, _, _, _⟩ := modelCategoryQuillen.exists_injective_resolution K.obj n
  let L' : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ L inferInstance
  have hL' : L'.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    ext
    exact (L.isZero_of_isStrictlyGE n i).eq_of_src _ _
  exact ⟨⟨L', n, hL'⟩, hL', ObjectProperty.homMk i, by assumption⟩

end CochainComplex.Plus

namespace DerivedCategory.Plus

variable {C} [HasDerivedCategory C]

lemma exists_injective_resolution [EnoughInjectives C] (K : DerivedCategory.Plus C)
    (n : ℤ) [K.IsGE n] :
    ∃ (L : CochainComplex.Plus (InjectiveObject C)) (_ : L.obj.IsStrictlyGE n),
      Nonempty (DerivedCategory.Plus.Q.obj
        ((InjectiveObject.ι C).mapCochainComplexPlus.obj L) ≅ K) := by
  have : K.obj.IsGE n := (K.isGE_ι_obj_iff n).2 (by assumption)
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K.obj n
  obtain ⟨M, _, i, hi⟩ :=
    CochainComplex.Plus.exists_injective_resolution ⟨L, ⟨n, inferInstance⟩⟩ n
  have : QuasiIso i.hom := by assumption
  exact ⟨M, inferInstance,
    ⟨DerivedCategory.Plus.ι.preimageIso ((asIso (DerivedCategory.Q.map i.hom)).symm ≪≫ e.symm)⟩⟩

end DerivedCategory.Plus

namespace CochainComplex.Plus

@[simps]
def localizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (quasiIso C) where
  functor := (InjectiveObject.ι C).mapCochainComplexPlus
  map := by rfl

instance : (localizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance (K : Plus (InjectiveObject C)) (n : ℤ) :
    Injective (K.obj.X n).obj :=
  (K.obj.X n).property

variable [EnoughInjectives C]

open modelCategoryQuillen

instance (K : FibrantObject (Plus C)) (n : ℤ) :
    Injective (K.obj.obj.X n) := by
  obtain ⟨K, hK⟩ := K
  rw [fibrantObjects, modelCategoryQuillen.isFibrant_iff] at hK
  dsimp
  infer_instance

def fibrantObjectEquivalence :
    Plus (InjectiveObject C) ≌ FibrantObject (Plus C) where
  functor := ObjectProperty.lift _ (InjectiveObject.ι C).mapCochainComplexPlus (fun K ↦ by
    dsimp [fibrantObjects]
    rw [modelCategoryQuillen.isFibrant_iff]
    intro n
    dsimp
    infer_instance)
  inverse := ObjectProperty.lift _
    (HomologicalComplex.liftFunctorObjectProperty _ (FibrantObject.ι ⋙ Plus.ι C)
      (fun K n ↦ by dsimp; infer_instance)) (by
        rintro ⟨⟨K, n, hn⟩, _⟩
        refine ⟨n, ?_⟩
        rw [isStrictlyGE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero]
        ext
        apply (K.isZero_of_isStrictlyGE n i hi).eq_of_tgt)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simps]
def fibrantObjectLocalizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (weakEquivalences (FibrantObject (Plus C))) where
  functor := (fibrantObjectEquivalence C).functor
  map := by rfl

instance : (fibrantObjectLocalizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance : (fibrantObjectLocalizerMorphism C).functor.IsEquivalence := by
  dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : (localizerMorphism C).IsRightDerivabilityStructure := by
  rw [LocalizerMorphism.isRightDerivabilityStructure_iff_of_equivalences
    (T := localizerMorphism C) (B := (FibrantObject.localizerMorphism (Plus C)))
    (R := .id _) (L := fibrantObjectLocalizerMorphism C) (Iso.refl _)]
  infer_instance

end CochainComplex.Plus

namespace HomotopyCategory.Plus

@[simps]
def localizerMorphism : LocalizerMorphism
  (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C)))
    (HomotopyCategory.Plus.quasiIso C) where
  functor := (InjectiveObject.ι C).mapHomotopyCategoryPlus
  map K L f (hf : IsIso f) := by
    dsimp only [MorphismProperty.inverseImage, HomotopyCategory.Plus.quasiIso]
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    infer_instance

set_option backward.isDefEq.respectTransparency false in
variable {C} in
lemma isIso_quotient_map
    {K L : CochainComplex.Plus (InjectiveObject C)} (f : K ⟶ L) :
    IsIso ((quotient _).map f) ↔
    CochainComplex.Plus.quasiIso C ((InjectiveObject.ι C).mapCochainComplexPlus.map f) := by
  rw [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι (InjectiveObject C)),
    ← isIso_iff_of_reflects_iso _ (Functor.mapHomotopyCategory (InjectiveObject.ι C) (.up ℤ))]
  dsimp
  rw [CochainComplex.IsKInjective.isIso_quotient_map_iff_quasiIso]
  rfl

namespace isRightDerivabilityStructure

open MorphismProperty

@[simps]
def L : LocalizerMorphism
  ((CochainComplex.Plus.quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (isomorphisms (Plus (InjectiveObject C))) where
  functor := HomotopyCategory.Plus.quotient (InjectiveObject C)
  map _ _ f hf := (isIso_quotient_map f).2 hf

instance : (L C).IsInduced where
  inverseImage_eq := by ext; apply isIso_quotient_map

set_option backward.isDefEq.respectTransparency false in
@[simps]
def R : LocalizerMorphism (CochainComplex.Plus.quasiIso C) (quasiIso C) where
  functor := HomotopyCategory.Plus.quotient C
  map := by
    intro X Y f hf
    simpa [quasiIso, quotient_map_mem_quasiIso_iff]

instance : (R C).IsInduced where
  inverseImage_eq := by ext; apply quotient_map_mem_quasiIso_iff

set_option backward.isDefEq.respectTransparency false in
open HomologicalComplex in
lemma inverseImage_quasiIso_mapCochainComplexPlus_injectivesι :
    (CochainComplex.Plus.quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus =
    (homotopyEquivalences (InjectiveObject C) (ComplexShape.up ℤ)).inverseImage
      (CochainComplex.Plus.ι (InjectiveObject C)) := by
  ext K L f
  simp [CochainComplex.Plus.quasiIso, Functor.mapCochainComplexPlus,
    ← CochainComplex.IsKInjective.isIso_quotient_map_iff_quasiIso,
    ← isIso_quotient_map_iff_homotopyEquivalences,
    ← isIso_iff_of_reflects_iso _ ((InjectiveObject.ι C).mapHomotopyCategory (.up ℤ))]

instance : (HomotopyCategory.Plus.quotient (InjectiveObject C)).IsLocalization
      ((CochainComplex.Plus.quasiIso C).inverseImage
      (InjectiveObject.ι C).mapCochainComplexPlus) := by
  rw [inverseImage_quasiIso_mapCochainComplexPlus_injectivesι]
  infer_instance

instance : (L C).IsLocalizedEquivalence := by
  have :
      ((L C).functor ⋙ 𝟭 (Plus (InjectiveObject C))).IsLocalization
        ((CochainComplex.Plus.quasiIso C).inverseImage
          (InjectiveObject.ι C).mapCochainComplexPlus) :=
    inferInstanceAs ((HomotopyCategory.Plus.quotient (InjectiveObject C)).IsLocalization _)
  exact LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization (L C) (𝟭 _)

set_option backward.isDefEq.respectTransparency false in
open HomologicalComplex in
instance {D : Type*} [Category* D] (L : Plus C ⥤ D) [L.IsLocalization (quasiIso C)] :
    (quotient C ⋙ L).IsLocalization (CochainComplex.Plus.quasiIso C) := by
  refine Functor.IsLocalization.comp _ _
    ((homotopyEquivalences C (.up ℤ)).inverseImage (CochainComplex.Plus.ι C))
    (quasiIso C) _ ?_ ?_ ?_
  · intro _ _ f hf
    refine Localization.inverts L (quasiIso C) _ ?_
    simpa [quasiIso, quotient_map_mem_quasiIso_iff]
  · intro K L f hf
    exact homotopyEquivalences_le_quasiIso _ _ _ hf
  · rintro K L f hf
    obtain ⟨K, rfl⟩ := Plus.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := Plus.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (Plus.quotient C).map_surjective f
    apply MorphismProperty.map_mem_map
    simpa [quasiIso, HomotopyCategory.quotient_map_mem_quasiIso_iff] using hf

instance {D : Type*} [Category* D] (L : Plus C ⥤ D) [L.IsLocalization (quasiIso C)] :
    ((R C).functor ⋙ L).IsLocalization (CochainComplex.Plus.quasiIso C) := by
  dsimp; infer_instance

instance : (R C).IsLocalizedEquivalence :=
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization
    (R C) ((quasiIso C).Q)

instance : (L C).functor.Full := by dsimp; infer_instance
instance : (R C).functor.Full := by dsimp; infer_instance
instance : (L C).functor.EssSurj := by dsimp; infer_instance
instance : (R C).functor.EssSurj := by dsimp; infer_instance

def iso : (CochainComplex.Plus.localizerMorphism C).functor ⋙
  (R C).functor ≅ (L C).functor ⋙ (localizerMorphism C).functor := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
open HomologicalComplex CochainComplex in
instance : TwoSquare.GuitartExact (iso C).hom :=
  TwoSquare.GuitartExact.quotient' (iso C).symm (by
    rintro ⟨K₁, n₁, hn₁⟩ ⟨K₂, n₂, hn₂⟩ f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    dsimp [Functor.mapCochainComplexPlus] at f₀ f₁
    refine ⟨⟨K₂.pathObject, CochainComplex.plus_pathObject K₂ ⟨n₂, hn₂⟩⟩,
      ObjectProperty.homMk (pathObject.π₀ K₂),
      ObjectProperty.homMk (pathObject.π₁ K₂),
      ?_, ObjectProperty.homMk ?_, ?_⟩
    · ext : 1
      exact eq_of_homotopy _ _ (pathObject.homotopy₀₁ _ (fun n ↦ ⟨n + 1, by simp⟩))
    · exact pathObject.lift f₀ f₁ (homotopyOfEq _ _ ((HomotopyCategory.Plus.ι C).congr_map hf)) ≫
        (pathObject.mapHomologicalComplexObjIso K₂ (InjectiveObject.ι C)
          (fun n ↦ ⟨n + 1, by simp⟩)).inv
    · dsimp [Functor.mapCochainComplexPlus]
      cat_disch)

end isRightDerivabilityStructure

variable [EnoughInjectives C]

instance isRightDerivabilityStructure : (localizerMorphism C).IsRightDerivabilityStructure :=
  LocalizerMorphism.isRightDerivabilityStructure_of_isLocalizedEquivalence
    (isRightDerivabilityStructure.iso C)

set_option backward.isDefEq.respectTransparency false in
instance : (HomotopyCategory.Plus.localizerMorphism C).arrow.HasRightResolutions := by
  intro f
  obtain ⟨K₁, K₂, f, rfl⟩ := Arrow.mk_surjective f
  let r₁ : (HomotopyCategory.Plus.localizerMorphism C).RightResolution K₁ :=
    Classical.arbitrary _
  let r₂ : (HomotopyCategory.Plus.localizerMorphism C).RightResolution K₂ :=
    Classical.arbitrary _
  obtain ⟨φ, hφ⟩ : ∃ φ, r₁.w ≫ φ = f ≫ r₂.w := by
    obtain ⟨α, hα⟩ :=
      (HomotopyCategory.quotient _ _).map_surjective ((HomotopyCategory.Plus.ι C).map r₁.w)
    let L := ((InjectiveObject.ι C).mapHomologicalComplex _).obj r₂.X₁.obj.as
    have : QuasiIso α := by
      change HomologicalComplex.quasiIso C _ α
      rw [← quotient_map_mem_quasiIso_iff, hα]
      exact r₁.hw
    have (n : ℤ) : Injective (L.X n) := (r₂.X₁.obj.as.X n).property
    obtain ⟨d, hd⟩ := r₂.X₁.property
    have := CochainComplex.isKInjective_of_injective L d
    obtain ⟨β, hβ⟩ := (CochainComplex.IsKInjective.bijective_precomp α L).2
      ((HomotopyCategory.Plus.ι C).map (f ≫ r₂.w))
    exact ⟨ObjectProperty.homMk β, (ι C).map_injective (by rw [← hβ, hα]; dsimp)⟩
  obtain ⟨φ, rfl⟩ := (InjectiveObject.ι C).mapHomotopyCategoryPlus.map_surjective φ
  exact ⟨{
    X₁ := Arrow.mk φ
    w := Arrow.homMk r₁.w r₂.w hφ
    hw := ⟨r₁.hw, r₂.hw⟩
  }⟩

noncomputable instance : (HomotopyCategory.Plus.localizerMorphism C).functor.CommShift ℤ := by
  dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : (HomotopyCategory.Plus.localizerMorphism C).functor.IsTriangulated := by
  dsimp; infer_instance

instance [HasDerivedCategory C] :
    ((InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).EssSurj where
  mem_essImage K := by
    let r : (HomotopyCategory.Plus.localizerMorphism C).RightResolution
        (DerivedCategory.Plus.Qh.objPreimage K) := Classical.arbitrary _
    have := Localization.inverts DerivedCategory.Plus.Qh _ _ r.hw
    exact ⟨r.X₁, ⟨(asIso (DerivedCategory.Plus.Qh.map r.w)).symm ≪≫
      DerivedCategory.Plus.Qh.objObjPreimageIso K⟩⟩

section

variable (F : HomotopyCategory.Plus C ⥤ H)

variable {C} in
omit [EnoughInjectives C] in
lemma localizerMorphism_derives : (localizerMorphism C).Derives F :=
  MorphismProperty.isomorphisms_isInvertedBy _

/-- Any functor the homotopy category `K^+` has a right derived functor with respect
to quasi-isomorphisms. -/
instance : F.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso C) :=
  (localizerMorphism_derives F).hasPointwiseRightDerivedFunctor

variable [HasDerivedCategory C]
variable (F' : DerivedCategory.Plus C ⥤ H) (α : F ⟶ DerivedCategory.Plus.Qh ⋙ F')
  [F'.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]

instance (K : HomotopyCategory.Plus C) [(∀ (n : ℤ), Injective (K.obj.as.X n))] :
    IsIso (α.app K) := by
  have (Y : HomotopyCategory.Plus (InjectiveObject C)) :
      IsIso (α.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj Y)) :=
    (localizerMorphism_derives F).isIso_of_isRightDerivedFunctor _ _
  obtain ⟨Y, ⟨e⟩⟩ : (InjectiveObject.ι C).mapHomotopyCategoryPlus.essImage K :=
    ⟨(quotient _).obj
      ((CochainComplex.Plus.fibrantObjectEquivalence C).inverse.obj ⟨⟨_, K.property⟩, by
          dsimp [fibrantObjects]
          rw [CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff]
          infer_instance⟩), ⟨Iso.refl _⟩⟩
  rw [← NatTrans.isIso_app_iff_of_iso α e]
  infer_instance

example (X : HomotopyCategory.Plus (InjectiveObject C)) :
    IsIso ((F.totalRightDerivedUnit DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)).app
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X)) := by
  infer_instance

end

end HomotopyCategory.Plus
