/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Category.Cat

/-!
# Adjunctions in `Cat`

-/

universe v u

namespace CategoryTheory

open Bicategory

section

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')

attribute [local simp] bicategoricalComp Cat.associator_hom_app Cat.associator_inv_app
  Cat.leftUnitor_hom_app Cat.leftUnitor_inv_app Cat.rightUnitor_hom_app Cat.rightUnitor_inv_app
  Functor.toCatHom

namespace Adjunction

/-- The adjunction in the bicategorical sense attached to an adjunction between functors. -/
abbrev toCat : Bicategory.Adjunction F.toCatHom G.toCatHom where
  unit := adj.unit
  counit := adj.counit

/-- The adjunction of functors corresponding to an adjunction in the bicategory `Cat`. -/
abbrev ofCat {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) :
    Functor.ofCatHom F ⊣ Functor.ofCatHom G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by simpa using congr_app adj.left_triangle X
  right_triangle_components X := by simpa using congr_app adj.right_triangle X

@[simp]
lemma toCat_ofCat
    {C D : Cat} {F : C ⟶ D} {G : D ⟶ C} (adj : Bicategory.Adjunction F G) :
    (Adjunction.ofCat adj).toCat = adj := rfl

@[simp]
lemma ofCat_toCat :
    Adjunction.ofCat adj.toCat = adj := rfl

lemma toCat_comp_toCat : adj.toCat.comp adj'.toCat = (adj.comp adj').toCat := by
  cat_disch

end Adjunction

end

namespace Bicategory

@[simp]
lemma Adjunction.toCat_id (C : Cat.{v, u}) :
    Adjunction.ofCat (Adjunction.id C) = CategoryTheory.Adjunction.id :=
  rfl

lemma mateEquiv_eq_categoryTheoryMateEquiv {C D E F : Cat}
    {G : C ⟶ E} {H : D ⟶ F} {L₁ : C ⟶ D} {R₁ : D ⟶ C} {L₂ : E ⟶ F} {R₂ : F ⟶ E}
    (adj₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂)
    (f : G ≫ L₂ ⟶ L₁ ≫ H) :
    Bicategory.mateEquiv adj₁ adj₂ f =
      CategoryTheory.mateEquiv (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f := by
  ext X
  simp [mateEquiv, Adjunction.homEquiv₁, Adjunction.homEquiv₂, Functor.ofCatHom,
    Cat.rightUnitor_inv_app, Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app]

lemma conjugateEquiv_eq_categoryTheoryConjugateEquiv {C D : Cat}
    {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C}
    (adj₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂) (f : L₂ ⟶ L₁) :
    Bicategory.conjugateEquiv adj₁ adj₂ f =
      CategoryTheory.conjugateEquiv (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f := by
  dsimp [Bicategory.conjugateEquiv]
  rw [mateEquiv_eq_categoryTheoryMateEquiv]
  ext X
  simp [CategoryTheory.conjugateEquiv, Functor.ofCatHom,
    Cat.rightUnitor_inv_app, Cat.leftUnitor_hom_app]

end Bicategory

end CategoryTheory
