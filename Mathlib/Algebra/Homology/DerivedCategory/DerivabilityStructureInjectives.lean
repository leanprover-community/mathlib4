/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.Algebra.Homology.ModelCategory.Injective
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
public import Mathlib.CategoryTheory.GuitartExact.Quotient
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject

/-!
# The injective derivability structure

Let `C` be an abelian category with enough injectives.
In this file, we define a localizer morphism `CochainComplex.Plus.localizerMorphism`
(relative to quasi-isomorphisms) which is given by the (fully faithful) functor
`CochainComplex.Plus (InjectiveObject C) ⥤ CochainComplex.Plus C`, and we show
that it is a right derivability structure. (The proof proceeds by showing that
up to equivalences of categories, this functor is the inclusion of the full
subcategory of fibrant objects in the model category `CochainComplex.Plus C`.)

We also obtain a similar right derivability structure `HomotopyCategory.Plus.localizerMorphism`
for the functor `HomotopyCategory.Plus (InjectiveObject C) ⥤ HomotopyCategory.Plus C`, where
the target category is equipped with the class of quasi-isomorphisms while
the source category `HomotopyCategory.Plus (InjectiveObject C)` is equipped
with the class of isomorphisms (which is exactly the same as quasi-isomorphisms).
The consequence is that any functor from the category `HomotopyCategory.Plus C`
has a right derived functor, and we show that the unit natural transformation for
such a derived functor is an isomorphism on objects coming from
`HomotopyCategory.Plus (InjectiveObject C)`.

-/

@[expose] public section

open HomotopicalAlgebra CategoryTheory Limits

variable {C H : Type*} [Category* C] [Abelian C] [Category* H]

namespace CochainComplex.Plus

instance (X : HomotopyCategory.Plus (InjectiveObject C)) (n : ℤ) :
    Injective (((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X).obj.as.X n) :=
  inferInstanceAs (Injective ((InjectiveObject.ι C).obj (X.obj.as.X n)))

set_option backward.defeqAttrib.useBackward true in
instance (K : CochainComplex.Plus (InjectiveObject C)) :
    CochainComplex.IsKInjective
      (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K.obj) := by
  obtain ⟨K, n, hn⟩ := K
  let L := ((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K
  have (n : ℤ) : Injective (L.X n) := by dsimp [L]; infer_instance
  exact CochainComplex.isKInjective_of_injective L n

lemma exists_quasiIso_injective [EnoughInjectives C]
    (K : CochainComplex.Plus C) (n : ℤ) [K.obj.IsStrictlyGE n] :
    ∃ (L : CochainComplex.Plus (InjectiveObject C)) (_ : L.obj.IsStrictlyGE n)
      (i : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L),
        quasiIso C i := by
  obtain ⟨L, i, _, _, _⟩ := modelCategoryQuillen.exists_quasiIso_injective K.obj n
  let L' : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ L inferInstance
  have hL' : L'.IsStrictlyGE n := by
    rwa [← isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι _)]
  exact ⟨⟨L', n, hL'⟩, hL', ObjectProperty.homMk i, by assumption⟩

end CochainComplex.Plus

namespace DerivedCategory.Plus

variable [HasDerivedCategory C]

/-- Let `K` be an object in the bounded below derived category of an abelian category `C`
with enough injectives. Assume that `K` is cohomologically `≥ n`. Then, `K`
admits an "injective resolution", in the sense that there exists a cochain
complex `L` consisting of injective object and lying in degrees `≥ n`, such that `K`
is isomorphic to the image of `L`. -/
lemma exists_injective_nonempty_iso [EnoughInjectives C] (K : DerivedCategory.Plus C)
    (n : ℤ) [K.IsGE n] :
    ∃ (L : CochainComplex.Plus (InjectiveObject C)) (_ : L.obj.IsStrictlyGE n),
      Nonempty (DerivedCategory.Plus.Q.obj
        ((InjectiveObject.ι C).mapCochainComplexPlus.obj L) ≅ K) := by
  have : K.obj.IsGE n := (K.isGE_ι_obj_iff n).2 (by assumption)
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K.obj n
  obtain ⟨M, _, i, hi⟩ :=
    CochainComplex.Plus.exists_quasiIso_injective ⟨L, ⟨n, inferInstance⟩⟩ n
  have : QuasiIso i.hom := by assumption
  exact ⟨M, inferInstance,
    ⟨DerivedCategory.Plus.ι.preimageIso ((asIso (DerivedCategory.Q.map i.hom)).symm ≪≫ e.symm)⟩⟩

end DerivedCategory.Plus

namespace CochainComplex.Plus

variable (C) in
/-- The localizer morphism (relative to quasi-isomorphisms) that is
given by the "inclusion functor"
`CochainComplex.Plus (InjectiveObject C) ⥤ CochainComplex.Plus C`. -/
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
  infer_instance

variable (C) in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence between `CochainComplex.Plus (InjectiveObject C)`
and the category of fibrant object in `CochainComplex.Plus C` for the
Quillen model category structure. -/
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
        rwa [← isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι _)])
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable (C) in
/-- The localizer morphism (relative to quasi-isomorphisms) that is
given by the equivalence of categories
`CochainComplex.Plus (InjectiveObject C) ≌ FibrantObject (CochainComplex.Plus C)`. -/
abbrev fibrantObjectLocalizerMorphism :
    LocalizerMorphism ((quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (weakEquivalences (FibrantObject (Plus C))) where
  functor := (fibrantObjectEquivalence C).functor
  map := by rfl

instance : (fibrantObjectLocalizerMorphism C).IsInduced where
  inverseImage_eq := rfl

set_option backward.isDefEq.respectTransparency false in
instance : (localizerMorphism C).IsRightDerivabilityStructure := by
  rw [LocalizerMorphism.isRightDerivabilityStructure_iff_of_equivalences
    (T := localizerMorphism C) (B := FibrantObject.localizerMorphism (Plus C))
    (R := .id _) (L := fibrantObjectLocalizerMorphism C) (Iso.refl _)]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : (localizerMorphism C).arrow.HasRightResolutions := by
  rw [LocalizerMorphism.hasRightResolutions_arrow_iff_of_equivalences
    (T := localizerMorphism C) (B := FibrantObject.localizerMorphism (Plus C))
    (R := .id _) (L := fibrantObjectLocalizerMorphism C) (Iso.refl _)]
  infer_instance

end CochainComplex.Plus

namespace HomotopyCategory.Plus

variable (C) in
/-- The localizer morphism that is given by the "inclusion functor"
`HomotopyCategory.Plus (InjectiveObject C) ⥤ HomotopyCategory.Plus C`.
The target category is equipped with the class of quasi-isomorphisms while
the source category `HomotopyCategory.Plus (InjectiveObject C)` is equipped
with the class of isomorphisms (which is exactly the same as quasi-isomorphisms). -/
abbrev localizerMorphism : LocalizerMorphism
  (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C)))
    (HomotopyCategory.Plus.quasiIso C) where
  functor := (InjectiveObject.ι C).mapHomotopyCategoryPlus
  map K L f (hf : IsIso f) := by
    dsimp only [MorphismProperty.inverseImage, HomotopyCategory.Plus.quasiIso]
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma isIso_quotient_map_iff
    {K L : CochainComplex.Plus (InjectiveObject C)} (f : K ⟶ L) :
    IsIso ((quotient _).map f) ↔
    CochainComplex.Plus.quasiIso C ((InjectiveObject.ι C).mapCochainComplexPlus.map f) := by
  rw [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι (InjectiveObject C)),
    ← isIso_iff_of_reflects_iso _ (Functor.mapHomotopyCategory (InjectiveObject.ι C) (.up ℤ))]
  dsimp
  rw [HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences,
    ← CochainComplex.IsKInjective.quasiIso_iff]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open HomologicalComplex in
lemma inverseImage_quasiIso_mapCochainComplexPlus_injectiveObjectι :
    (CochainComplex.Plus.quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus =
    (homotopyEquivalences (InjectiveObject C) (.up ℤ)).inverseImage
      (CochainComplex.Plus.ι (InjectiveObject C)) := by
  ext K L f
  simp [CochainComplex.Plus.quasiIso, Functor.mapCochainComplexPlus,
    ← HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences,
    CochainComplex.IsKInjective.quasiIso_iff,
    ← isIso_iff_of_reflects_iso _ ((InjectiveObject.ι C).mapHomotopyCategory (.up ℤ))]

instance :
    (HomotopyCategory.Plus.quotient (InjectiveObject C)).IsLocalization
      ((CochainComplex.Plus.quasiIso C).inverseImage
      (InjectiveObject.ι C).mapCochainComplexPlus) := by
  rw [inverseImage_quasiIso_mapCochainComplexPlus_injectiveObjectι]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
open HomologicalComplex in
instance (L : Plus C ⥤ H) [L.IsLocalization (quasiIso C)] :
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
    simpa [quasiIso, quotient_map_mem_quasiIso_iff] using! hf

namespace isRightDerivabilityStructure

/-! The following private definitions are used to deduce that
`HomotopyCategory.Plus.localizerMorphism` is a right derivability structure
from the fact that `CochainComplex.Plus.localizerMorphism` is.

The strategy is to observe that the following commutative square
of localizer morphisms gives a Guitart exact square:
```
                           CochainComplex.Plus.localizerMorphism C
CochainComplex.Plus (InjectiveObject C) ----------> CochainComplex.Plus C
     |                                                        |
 L C |                                                        | R C
     v                                                        v
HomotopyCategory.Plus (InjectiveObject C) --------> HomotopyCategory.Plus C
                           HomotopyCategory.Plus.localizerMorphism C
```
That the square is Guitart exact will follow from the lemma
`TwoSquare.GuitartExact.quotient_of_nonempty_rightHomotopy`
from the file `Mathlib/CategoryTheory/GuitartExact/Quotient.lean`.

-/

open MorphismProperty

variable (C) in
/-- The left localizer morphism in the Guitart exact square `iso`. -/
private abbrev L : LocalizerMorphism
    ((CochainComplex.Plus.quasiIso C).inverseImage (InjectiveObject.ι C).mapCochainComplexPlus)
      (isomorphisms (Plus (InjectiveObject C))) where
  functor := HomotopyCategory.Plus.quotient (InjectiveObject C)
  map _ _ f hf := (isIso_quotient_map_iff f).2 hf

private instance : (L C).IsInduced where
  inverseImage_eq := by ext; apply isIso_quotient_map_iff

variable (C) in
set_option backward.isDefEq.respectTransparency false in
/-- The right localizer morphism in the Guitart exact square `iso`. -/
private abbrev R : LocalizerMorphism (CochainComplex.Plus.quasiIso C) (quasiIso C) where
  functor := HomotopyCategory.Plus.quotient C
  map _ _ _ _ := by simpa [quasiIso, quotient_map_mem_quasiIso_iff]

private instance : (R C).IsInduced where
  inverseImage_eq := by ext; apply quotient_map_mem_quasiIso_iff

private instance : (L C).IsLocalizedEquivalence := by
  have :
      ((L C).functor ⋙ 𝟭 (Plus (InjectiveObject C))).IsLocalization
        ((CochainComplex.Plus.quasiIso C).inverseImage
          (InjectiveObject.ι C).mapCochainComplexPlus) :=
    inferInstanceAs ((HomotopyCategory.Plus.quotient (InjectiveObject C)).IsLocalization _)
  exact LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization (L C) (𝟭 _)

private instance : (R C).IsLocalizedEquivalence :=
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization
    (R C) ((quasiIso C).Q)

variable (C) in
/-- The "commutative" square of functors involving the underlying functors
of the localizer morphisms `CochainComplex.Plus.localizerMorphism C`
and `HomotopyCategory.Plus.localizerMorphism C`. -/
private def iso :
    (CochainComplex.Plus.localizerMorphism C).functor ⋙ (R C).functor ≅
    (L C).functor ⋙ (localizerMorphism C).functor := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
open HomologicalComplex CochainComplex in
private instance : TwoSquare.GuitartExact (iso C).hom :=
  TwoSquare.GuitartExact.quotient_of_nonempty_rightHomotopy (iso C).symm (by
    rintro ⟨K₁, n₁, hn₁⟩ ⟨K₂, n₂, hn₂⟩ f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    dsimp [Functor.mapCochainComplexPlus] at f₀ f₁
    refine ⟨Plus.prepathObject _, ?_, ⟨?_⟩⟩
    · ext : 1
      exact eq_of_homotopy _ _ (pathObject.homotopy₀₁ _ (fun n ↦ ⟨n + 1, by simp⟩))
    · refine PrepathObject.RightHomotopy.fullSubcategoryEquiv.symm
        { h := pathObject.lift f₀ f₁ (homotopyOfEq _ _
          ((HomotopyCategory.Plus.ι C).congr_map hf)) ≫
          (pathObject.mapHomologicalComplexObjIso K₂ (InjectiveObject.ι C)
            (fun n ↦ ⟨n + 1, by simp⟩)).inv
          h₀ := ?_
          h₁ := ?_ }
      all_goals
        dsimp [Functor.mapCochainComplexPlus]
        cat_disch)

end isRightDerivabilityStructure

variable [EnoughInjectives C]

instance isRightDerivabilityStructure : (localizerMorphism C).IsRightDerivabilityStructure :=
  LocalizerMorphism.isRightDerivabilityStructure_of_isLocalizedEquivalence
    (isRightDerivabilityStructure.iso C)

instance : (HomotopyCategory.Plus.localizerMorphism C).arrow.HasRightResolutions :=
  LocalizerMorphism.hasRightResolutions_arrow_of_essSurj_of_full
    (isRightDerivabilityStructure.iso C)

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

omit [EnoughInjectives C] in
lemma localizerMorphism_derives : (localizerMorphism C).Derives F :=
  MorphismProperty.isInvertedBy_isomorphisms _

/-- Any functor from the bounded below homotopy category has a right derived functor
with respect to quasi-isomorphisms. -/
instance : F.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso C) :=
  (localizerMorphism_derives F).hasPointwiseRightDerivedFunctor

variable [HasDerivedCategory C] (F' : DerivedCategory.Plus C ⥤ H)
  (α : F ⟶ DerivedCategory.Plus.Qh ⋙ F')
  [F'.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]

instance (K : HomotopyCategory.Plus C) [(∀ (n : ℤ), Injective (K.obj.as.X n))] :
    IsIso (α.app K) := by
  have (Y : HomotopyCategory.Plus (InjectiveObject C)) :
      IsIso (α.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj Y)) :=
    (localizerMorphism_derives F).isIso_of_isRightDerivedFunctor _ _
  obtain ⟨Y, ⟨e⟩⟩ : (InjectiveObject.ι C).mapHomotopyCategoryPlus.essImage K := by
    obtain ⟨X, hX⟩ := K
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    refine ⟨(quotient _).obj
      ((CochainComplex.Plus.fibrantObjectEquivalence C).inverse.obj
      ⟨⟨K, by simpa using hX⟩, ?_⟩), ⟨Iso.refl _⟩⟩
    dsimp [fibrantObjects]
    rwa [CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff]
  rw [← NatTrans.isIso_app_iff_of_iso α e]
  infer_instance

example (X : HomotopyCategory.Plus (InjectiveObject C)) :
    IsIso ((F.totalRightDerivedUnit DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)).app
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X)) := by
  infer_instance

end

end HomotopyCategory.Plus
