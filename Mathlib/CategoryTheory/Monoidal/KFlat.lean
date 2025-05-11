/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Monoidal
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# K-flat objects

-/

namespace CategoryTheory

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D]

open MonoidalCategory

namespace MorphismProperty

variable (W : MorphismProperty C) (L : C ⥤ D)

def kFlat : ObjectProperty C := fun X ↦
  ObjectProperty.localizerMorphism W W (tensorLeft X) ∧
    ObjectProperty.localizerMorphism W W (tensorRight X)

instance [W.RespectsIso] : W.kFlat.IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨h₁, h₂⟩
    exact ⟨(ObjectProperty.localizerMorphism W W).prop_of_iso ((curriedTensor C).mapIso e) h₁,
      (ObjectProperty.localizerMorphism W W).prop_of_iso ((curriedTensor C).flip.mapIso e) h₂⟩

section

variable {W}

lemma kFlat.whiskerLeft {X Y₁ Y₂ : C} (hX : W.kFlat X)
    {f : Y₁ ⟶ Y₂} (hf : W f) : W (X ◁ f) :=
  hX.1 _ hf

lemma kFlat.whiskerRight {Y X₁ X₂ : C} (hY : W.kFlat Y)
    {f : X₁ ⟶ X₂} (hf : W f) : W (f ▷ Y) :=
  hY.2 _ hf

end

instance [W.RespectsIso] : W.kFlat.IsMonoidal where
  prop_unit :=
    ⟨fun _ _ _ hf ↦ (W.arrow_mk_iso_iff (Arrow.isoMk (λ_ _) (λ_ _))).2 hf,
      fun _ _ _ hf ↦ (W.arrow_mk_iso_iff (Arrow.isoMk (ρ_ _) (ρ_ _))).2 hf⟩
  prop_tensor X₁ X₂ hX₁ hX₂ :=
    ⟨fun _ _ _ hf ↦ (W.arrow_mk_iso_iff
        (Arrow.isoMk (α_ _ _ _) (α_ _ _ _))).2 (hX₁.whiskerLeft (hX₂.whiskerLeft hf)),
      fun _ _ _ hf ↦ (W.arrow_mk_iso_iff
        (Arrow.isoMk (α_ _ _ _) (α_ _ _ _))).1 (hX₂.whiskerRight (hX₁.whiskerRight hf))⟩

abbrev KFlat := W.kFlat.FullSubcategory

abbrev ιKFlat : W.KFlat ⥤ C := W.kFlat.ι

def WKFlat : MorphismProperty W.KFlat := W.inverseImage W.ιKFlat

instance [W.ContainsIdentities] : W.WKFlat.ContainsIdentities := by
  dsimp only [WKFlat]
  infer_instance

@[simps]
def localizerMorphismKFlat :
    LocalizerMorphism W.WKFlat W where
  functor := W.ιKFlat
  map := by rfl

instance : W.localizerMorphismKFlat.functor.Faithful := by dsimp; infer_instance
instance : W.localizerMorphismKFlat.functor.Full := by dsimp; infer_instance

instance [W.RespectsIso] :
    W.localizerMorphismKFlat.functor.Monoidal :=
  inferInstanceAs W.ιKFlat.Monoidal

lemma whiskerRight_of_kFlat [W.HasTwoOutOfThreeProperty]
    [W.localizerMorphismKFlat.HasLeftResolutions]
    {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (hX₁ : W.kFlat X₁) (hX₂ : W.kFlat X₂) (Y : C) :
    W (f ▷ Y) := by
  obtain ⟨Y', hY', g, hg⟩ : ∃ (Y' : C) (hY : W.kFlat Y') (g : Y' ⟶ Y), W g := by
    have R : W.localizerMorphismKFlat.LeftResolution Y := Classical.arbitrary _
    exact ⟨R.X₁.obj, R.X₁.property, R.w, R.hw⟩
  rw [← W.precomp_iff _ _ (hX₁.whiskerLeft hg), whisker_exchange f g]
  exact W.comp_mem _ _ (hY'.whiskerRight hf) (hX₂.whiskerLeft hg)

lemma whiskerLeft_of_kFlat [W.HasTwoOutOfThreeProperty]
    [W.localizerMorphismKFlat.HasLeftResolutions]
    {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) (hY₁ : W.kFlat Y₁) (hY₂ : W.kFlat Y₂) (X : C) :
    W (X ◁ g) := by
  obtain ⟨X', hX', f, hf⟩ : ∃ (X' : C) (hX : W.kFlat X') (f : X' ⟶ X), W f := by
    have R : W.localizerMorphismKFlat.LeftResolution X := Classical.arbitrary _
    exact ⟨R.X₁.obj, R.X₁.property, R.w, R.hw⟩
  rw [← W.precomp_iff _ _ (hY₁.whiskerRight hf), ← whisker_exchange f g]
  exact W.comp_mem _ _ (hX'.whiskerLeft hg) (hY₂.whiskerRight hf)

lemma kFlat_derivesMonoidal [W.ContainsIdentities] [L.IsLocalization W] :
    W.localizerMorphismKFlat.DerivesMonoidalStructure L := by
  dsimp only [LocalizerMorphism.DerivesMonoidalStructure]
  rw [LocalizerMorphism.derives₂_iff]
  exact ⟨fun X _ _ _ hf ↦ Localization.inverts L W _ (X.2.whiskerRight hf),
    fun X _ _ _ hf ↦ Localization.inverts L W _ (X.2.whiskerLeft hf)⟩

instance [W.RespectsIso] [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
    [L.IsLocalization W] [W.ContainsIdentities] :
    L.HasDerivedMonoidalCategory W :=
  (W.kFlat_derivesMonoidal L).hasDerivedMonoidalCategory

lemma kFlat_prod_id_derives_curriedTensor [W.ContainsIdentities] [W.HasTwoOutOfThreeProperty]
    [W.localizerMorphismKFlat.HasLeftResolutions] [L.IsLocalization W] :
    LocalizerMorphism.Derives₂ W.localizerMorphismKFlat (LocalizerMorphism.id W)
      (curriedTensor C ⋙ (whiskeringRight C C D).obj L) := by
  rw [LocalizerMorphism.derives₂_iff]
  exact ⟨fun X₂ X₁ Y₁ f hf ↦ by dsimp; exact Localization.inverts L W _ (W.whiskerRight_of_kFlat _
      hf X₁.property Y₁.property _),
    fun X₁ X₂ Y₂ g hg ↦ Localization.inverts L W _ (X₁.property.whiskerLeft hg)⟩

lemma id_prod_kFlat_derives_curriedTensor [W.ContainsIdentities] [W.HasTwoOutOfThreeProperty]
    [W.localizerMorphismKFlat.HasLeftResolutions] [L.IsLocalization W] :
    LocalizerMorphism.Derives₂ (LocalizerMorphism.id W) W.localizerMorphismKFlat
      (curriedTensor C ⋙ (whiskeringRight C C D).obj L) := by
  rw [LocalizerMorphism.derives₂_iff]
  exact ⟨fun X₂ X₁ Y₁ f hf ↦ Localization.inverts L W _ (X₂.property.whiskerRight hf),
    fun X₁ X₂ Y₂ g hg ↦ Localization.inverts L W _
      (W.whiskerLeft_of_kFlat _ hg X₂.property Y₂.property _)⟩

end MorphismProperty

namespace DerivedMonoidal

variable (L : C ⥤ D) (W : MorphismProperty C) [W.RespectsIso]
  [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
  [L.IsLocalization W] [W.ContainsIdentities]
  [W.HasTwoOutOfThreeProperty]

lemma isIso_counit_app_app_of_kFlat_right (X Y : C) (hY : W.kFlat Y) :
    IsIso (((counit L W).app X).app Y) :=
  have : (bifunctor L W).IsLeftDerivedFunctor₂ (counit L W) W W := inferInstance
  (W.id_prod_kFlat_derives_curriedTensor L).isIso_of_isLeftDerivabilityStructure _ X ⟨Y, hY⟩

lemma isIso_counit_app_app_of_kFlat_left (X Y : C) (hX : W.kFlat X) :
    IsIso (((counit L W).app X).app Y) :=
  have : (bifunctor L W).IsLeftDerivedFunctor₂ (counit L W) W W := inferInstance
  (W.kFlat_prod_id_derives_curriedTensor L).isIso_of_isLeftDerivabilityStructure _ ⟨X, hX⟩ Y

lemma isLeftDerivedFunctor_bifunctorCounit₁_kFlat (X : C) :
    Functor.IsLeftDerivedFunctor _ (Functor.bifunctorCounit₁ (counit L W) X) W :=
  W.localizerMorphismKFlat.isLeftDerivedFunctor_of_isLeftDerivabilityStructure _
    (fun Y ↦ isIso_counit_app_app_of_kFlat_right _ _ _ _ Y.property)

lemma isLeftDerivedFunctor_bifunctorCounit₂_kFlat (X : C) :
    Functor.IsLeftDerivedFunctor _ (Functor.bifunctorCounit₁ (counit L W) X) W :=
  W.localizerMorphismKFlat.isLeftDerivedFunctor_of_isLeftDerivabilityStructure _
    (fun Y ↦ isIso_counit_app_app_of_kFlat_right _ _ _ _ Y.property)

end DerivedMonoidal

end CategoryTheory
