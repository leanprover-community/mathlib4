/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Closed.Monoidal

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

attribute [local simp] enrichedCategorySelf_id enrichedCategorySelf_comp

section

variable {C}

/-- The morphism `𝟙_ C ⟶ (ihom X).obj Y` corresponding to a morphism `X ⟶ Y`. -/
def curry' {X Y : C} (f : X ⟶ Y) : 𝟙_ C ⟶ (ihom X).obj Y := curry ((ρ_ _).hom ≫ f)

/-- The morphism `X ⟶ Y` corresponding to a morphism `𝟙_ C ⟶ (ihom X).obj Y`. -/
def uncurry' {X Y : C} (g : 𝟙_ C ⟶ (ihom X).obj Y) : X ⟶ Y := (ρ_ _).inv ≫ uncurry g

/-- `curry'` and `uncurry`' are inverse bijections. -/
@[simp]
lemma curry'_uncurry' {X Y : C} (g : 𝟙_ C ⟶ (ihom X).obj Y) : curry' (uncurry' g) = g := by
  simp [curry', uncurry']

/-- `curry'` and `uncurry`' are inverse bijections. -/
@[simp]
lemma uncurry'_curry' {X Y : C} (f : X ⟶ Y) : uncurry' (curry' f) = f := by
  simp [curry', uncurry']

/-- The bijection `(X ⟶ Y) ≃ (𝟙_ C ⟶ (ihom X).obj Y)` in a monoidal closed category. -/
@[simps]
def curryHomEquiv' {X Y : C} : (X ⟶ Y) ≃ (𝟙_ C ⟶ (ihom X).obj Y) where
  toFun := curry'
  invFun := uncurry'
  left_inv _ := by simp
  right_inv _ := by simp

lemma curry'_injective {X Y : C} {f f' : X ⟶ Y} (h : curry' f = curry' f') : f = f' :=
  curryHomEquiv'.injective h

lemma uncurry'_injective {X Y : C} {f f' : 𝟙_ C ⟶ (ihom X).obj Y}
    (h : uncurry' f = uncurry' f') : f = f' :=
  curryHomEquiv'.symm.injective h

@[simp]
lemma curry'_id (X : C) : curry' (𝟙 X) = id X := by
  dsimp [curry']
  rw [Category.comp_id]
  rfl

@[reassoc]
lemma whiskerLeft_curry'_ihom_ev_app {X Y : C} (f : X ⟶ Y) :
    X ◁ curry' f ≫ (ihom.ev X).app Y = (ρ_ _).hom ≫ f := by
  dsimp [curry']
  simp only [whiskerLeft_curry_ihom_ev_app]

@[reassoc]
lemma curry'_whiskerRight_comp {X Y Z : C} (f : X ⟶ Y) :
    curry' f ▷ _ ≫ comp X Y Z = (λ_ _).hom ≫ (pre f).app Z := by
  rw [← cancel_epi (λ_ _).inv, Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_pre, comp_eq, ← curry_natural_left, ← curry_natural_left, uncurry_curry,
    compTranspose_eq, associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    whiskerLeft_curry'_ihom_ev_app, comp_whiskerRight_assoc, triangle_assoc_comp_right_assoc,
    whiskerLeft_inv_hom_assoc]

@[reassoc]
lemma whiskerLeft_curry'_comp {X Y Z : C} (f : Y ⟶ Z) :
    _ ◁ curry' f ≫ comp X Y Z = (ρ_ _).hom ≫ (ihom X).map f := by
  rw [← cancel_epi (ρ_ _).inv, Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_ihom_map, comp_eq, ← curry_natural_left, ← curry_natural_left, uncurry_curry,
    compTranspose_eq, associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  dsimp
  rw [whiskerLeft_curry'_ihom_ev_app, whiskerLeft_rightUnitor_inv,
    MonoidalCategory.whiskerRight_id_assoc, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,]

lemma curry'_ihom_map {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    curry' f ≫ (ihom X).map g = curry' (f ≫ g) := by
  simp only [curry', ← curry_natural_right, Category.assoc]

lemma curry'_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    curry' (f ≫ g) = (λ_ (𝟙_ C)).inv ≫ (curry' f ⊗ curry' g) ≫ comp X Y Z := by
  rw [tensorHom_def_assoc, whiskerLeft_curry'_comp, MonoidalCategory.whiskerRight_id,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← unitors_equal,
    Iso.inv_hom_id_assoc, curry'_ihom_map]

end

/-- A monoidal closed category is an enriched ordinary category over itself.  -/
scoped instance enrichedOrdinaryCategorySelf : EnrichedOrdinaryCategory C C where
  homEquiv := curryHomEquiv'
  homEquiv_id := curry'_id
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

lemma enrichedOrdinaryCategorySelf_homEquiv_symm {X Y : C} (g : 𝟙_ C ⟶ (ihom X).obj Y):
    (eHomEquiv C).symm g = uncurry' g := rfl

end MonoidalClosed

end CategoryTheory
