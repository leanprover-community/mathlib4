/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Adjunctions in `Cat`

We show that adjunctions in the bicategory `Cat` correspond to
adjunctions between functors in the usual categorical sense.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Bicategory

section

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')

namespace Adjunction

attribute [local simp] bicategoricalComp

/-- The adjunction in the bicategorical sense attached to an adjunction between functors. -/
@[simps]
def toCat : Bicategory.Adjunction F.toCatHom G.toCatHom where
  unit := .ofNatTrans adj.unit
  counit := .ofNatTrans adj.counit

/-- The adjunction of functors corresponding to an adjunction in the bicategory `Cat`. -/
@[simps]
def ofCat {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) :
    F.toFunctor ⊣ G.toFunctor where
  unit := adj.unit.toNatTrans
  counit := adj.counit.toNatTrans
  left_triangle_components X := by
    simpa using congr($(adj.left_triangle).toNatTrans.app X)
  right_triangle_components X := by
    simpa using congr($(adj.right_triangle).toNatTrans.app X)

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
lemma Adjunction.ofCat_id (C : Cat.{v, u}) :
    Adjunction.ofCat (Adjunction.id C) = CategoryTheory.Adjunction.id :=
  rfl

lemma Adjunction.ofCat_comp {C D E : Cat.{v, u}}
    {F : C ⟶ D} {G : D ⟶ C} (adj : F ⊣ G)
    {F' : D ⟶ E} {G' : E ⟶ D} (adj' : F' ⊣ G') :
    Adjunction.ofCat (adj.comp adj') = (Adjunction.ofCat adj).comp (Adjunction.ofCat adj') := by
  ext
  simp [bicategoricalComp]

lemma toNatTrans_mateEquiv {C D E F : Cat}
    {G : C ⟶ E} {H : D ⟶ F} {L₁ : C ⟶ D} {R₁ : D ⟶ C} {L₂ : E ⟶ F} {R₂ : F ⟶ E}
    (adj₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂)
    (f : G ≫ L₂ ⟶ L₁ ≫ H) :
    (Bicategory.mateEquiv adj₁ adj₂ f).toNatTrans =
      CategoryTheory.mateEquiv (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f.toNatTrans := by
  ext X
  simp [mateEquiv, Adjunction.homEquiv₁, Adjunction.homEquiv₂]

lemma toNatTrans_conjugateEquiv {C D : Cat}
    {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C}
    (adj₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂) (f : L₂ ⟶ L₁) :
    (Bicategory.conjugateEquiv adj₁ adj₂ f).toNatTrans =
      CategoryTheory.conjugateEquiv
        (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f.toNatTrans := by
  dsimp [Bicategory.conjugateEquiv]
  rw [toNatTrans_mateEquiv]
  ext X
  simp [CategoryTheory.conjugateEquiv]

end Bicategory

end CategoryTheory
