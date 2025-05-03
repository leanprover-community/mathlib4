/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.Monoidal.Derived
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# K-flat objects

-/

namespace CategoryTheory

variable {C D : Type*} [Category C] [MonoidalCategory C]
  [Category D] (L : C ⥤ D) (W : MorphismProperty C)
open MonoidalCategory

namespace MorphismProperty

def kFlat : ObjectProperty C := fun X ↦
  W ≤ W.inverseImage (tensorLeft X) ∧
    W ≤ W.inverseImage (tensorRight X)

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

def localizerMorphismKFlat :
    LocalizerMorphism W.WKFlat W where
  functor := W.ιKFlat
  map := by rfl

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

/-instance [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
    [L.IsLocalization W] [W.ContainsIdentities] :
    L.HasDerivedMonoidalCategory W := by
  -- this should follow from a general result about derivability
  -- structure `Φ` such that `Φ.functor` is monoidal
  sorry-/

end MorphismProperty

end CategoryTheory
