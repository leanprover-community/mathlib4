/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# A closed monoidal category is enriched in itself

From the data of a closed monoidal category `C`, we define a `C`-category structure for `C`.
where the hom-object is given by the internal hom (coming from the closed structure).

We use `scoped instance` to avoid potential issues where `C` may also have
a `C`-category structure coming from another source (e.g. the type of simplicial sets
`SSet.{v}` has an instance of `EnrichedCategory SSet.{v}` as a category of simplicial objects;
see `Mathlib/AlgebraicTopology/SimplicialCategory/SimplicialObject.lean`).

All structure field values are defined in `Mathlib/CategoryTheory/Closed/Monoidal.lean`.

-/
set_option backward.defeqAttrib.useBackward true

public section

universe u v

namespace CategoryTheory

open Category MonoidalCategory

namespace MonoidalClosed

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- For `C` closed monoidal, build an instance of `C` as a `C`-category -/
scoped instance enrichedCategorySelf : EnrichedCategory C C where
  Hom x := (ihom x).obj
  id _ := id _
  comp _ _ _ := comp _ _ _
  assoc _ _ _ _ := assoc _ _ _ _

section

variable {C}

lemma enrichedCategorySelf_hom (X Y : C) :
    EnrichedCategory.Hom X Y = (ihom X).obj Y := rfl

lemma enrichedCategorySelf_id (X : C) :
    eId C X = id X := rfl

lemma enrichedCategorySelf_comp (X Y Z : C) :
    eComp C X Y Z = comp X Y Z := rfl

end

/-- A monoidal closed category is an enriched ordinary category over itself. -/
scoped instance enrichedOrdinaryCategorySelf : EnrichedOrdinaryCategory C C where
  homEquiv := curryHomEquiv'
  homEquiv_id X := curry'_id X
  homEquiv_comp := curry'_comp

lemma enrichedOrdinaryCategorySelf_eHomWhiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    eHomWhiskerLeft C X g = (ihom X).map g := by
  change (ρ_ _).inv ≫ _ ◁ curry' g ≫ comp X Y₁ Y₂ = _
  rw [whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]

lemma enrichedOrdinaryCategorySelf_eHomWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    eHomWhiskerRight C f Y = (pre f).app Y := by
  change (λ_ _).inv ≫ curry' f ▷ _ ≫ comp X₁ X₂ Y = _
  rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]

lemma enrichedOrdinaryCategorySelf_homEquiv {X Y : C} (f : X ⟶ Y) :
    eHomEquiv C f = curry' f := rfl

lemma enrichedOrdinaryCategorySelf_homEquiv_symm {X Y : C} (g : 𝟙_ C ⟶ (ihom X).obj Y) :
    (eHomEquiv C).symm g = uncurry' g := rfl

end MonoidalClosed

end CategoryTheory
