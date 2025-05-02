/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.Monoidal.Derived
import Mathlib.CategoryTheory.Monoidal.Subcategory

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

instance [W.RespectsIso] : W.kFlat.IsMonoidal where
  prop_unit :=
    ⟨fun _ _ _ hf ↦ (W.arrow_mk_iso_iff (Arrow.isoMk (λ_ _) (λ_ _))).2 hf,
      fun _ _ _ hf ↦ (W.arrow_mk_iso_iff (Arrow.isoMk (ρ_ _) (ρ_ _))).2 hf⟩
  prop_tensor X₁ X₂ hX₁ hX₂ :=
    ⟨fun _ _ _ hf ↦ (W.arrow_mk_iso_iff
        (Arrow.isoMk (α_ _ _ _) (α_ _ _ _))).2 (hX₁.1 _ (hX₂.1 _ hf)),
      fun _ _ _ hf ↦ (W.arrow_mk_iso_iff
        (Arrow.isoMk (α_ _ _ _) (α_ _ _ _))).1 (hX₂.2 _ (hX₁.2 _ hf))⟩

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

/-instance [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
    [L.IsLocalization W] [W.ContainsIdentities] :
    L.HasDerivedMonoidalCategory W := by
  -- this should follow from a general result about derivability
  -- structure `Φ` such that `Φ.functor` is monoidal
  sorry-/

end MorphismProperty

end CategoryTheory
