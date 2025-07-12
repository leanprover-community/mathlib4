/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.DayConvolution

/-!
# Braidings for Day convolution

In this file, we show that if `C` is a braided monoidal category and
`V` also a braided monoidal category, then the day convolution monoidal structure
on `C ⥤ V` is
-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.MonoidalCategory.DayConvolution
open scoped ExternalProduct
open Opposite

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory V] [BraidedCategory V]
  (F G : C ⥤ V)

section

variable [DayConvolution F G] [DayConvolution G F]

/-- The natural transformation `F ⊠ G ⟶ (tensor C) ⋙ (G ⊛ F)` that corepresents
the braiding morphism `F ⊛ G ⟶ G ⊛ F`. -/
@[simps]
def braidingHomCorepresenting : F ⊠ G ⟶ tensor C ⋙ G ⊛ F where
  app _ := (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (G ⊛ F).map (β_ _ _).hom
  naturality {x y} f := by simp [tensorHom_def, ← Functor.map_comp]

/-- The natural transformation `F ⊠ G ⟶ (tensor C) ⋙ (G ⊛ F)` that corepresents
the braiding morphism `F ⊛ G ⟶ G ⊛ F`. -/
@[simps]
def braidingInvCorepresenting : G ⊠ F ⟶ tensor C ⋙ F ⊛ G where
  app _ := (β_ _ _).inv ≫ (unit F G).app (_, _) ≫ (F ⊛ G).map (β_ _ _).inv
  naturality {x y} f := by simp [tensorHom_def, ← Functor.map_comp]

/-- The braiding isomorphism for Day convolution. -/
def braiding : F ⊛ G ≅ G ⊛ F where
  hom := corepresentableBy F G|>.homEquiv.symm <| braidingHomCorepresenting F G
  inv := corepresentableBy G F|>.homEquiv.symm <| braidingInvCorepresenting F G
  hom_inv_id := by
    apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ G) (unit F G)
    ext
    simp [-tensor_obj]
  inv_hom_id := by
    apply Functor.hom_ext_of_isLeftKanExtension (G ⊛ F) (unit G F)
    ext
    simp [-tensor_obj]

@[reassoc (attr := simp)]
lemma unit_app_comp_braiding_hom (x y : C) :
    (unit F G).app (x, y) ≫ (braiding F G).hom.app (x ⊗ y) =
    (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (G ⊛ F).map (β_ _ _).hom := by
  change
    (unit F G).app (x, y) ≫ (braiding F G).hom.app ((tensor C).obj (x, y)) = _
  simp [braiding, braidingHomCorepresenting, -tensor_obj]

@[reassoc (attr := simp)]
lemma unit_app_comp_braiding_inv (x y : C) :
    (unit G F).app (x, y) ≫ (braiding F G).inv.app (x ⊗ y) =
    (β_ _ _).inv ≫ (unit F G).app (_, _) ≫ (F ⊛ G).map (β_ _ _).inv := by
  change
    (unit G F).app (x, y) ≫ (braiding F G).inv.app ((tensor C).obj (x, y)) = _
  simp [braiding, braidingHomCorepresenting, -tensor_obj]

end

variable {F G}

@[reassoc (attr := simp)]
lemma braiding_naturality_right (H : C ⥤ V) (η : F ⟶ G)
    [DayConvolution F H] [DayConvolution H F]
    [DayConvolution G H] [DayConvolution H G] :
    DayConvolution.map (𝟙 H) η ≫ (braiding H G).hom =
    (braiding H F).hom ≫ DayConvolution.map η (𝟙 H) := by
  apply Functor.hom_ext_of_isLeftKanExtension (H ⊛ F) (unit H F)
  ext ⟨_, _⟩
  simp

@[reassoc (attr := simp)]
lemma braiding_naturality_left (η : F ⟶ G) (H : C ⥤ V)
    [DayConvolution F H] [DayConvolution H F]
    [DayConvolution G H] [DayConvolution H G] :
    DayConvolution.map η (𝟙 H) ≫ (braiding G H).hom =
    (braiding F H).hom ≫ DayConvolution.map (𝟙 H) η := by
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ H) (unit F H)
  ext ⟨_, _⟩
  simp

lemma hexagon_forward {H : C ⥤ V} : 
    (associator F G H).hom ≫ (braiding F (G ⊗ H)).hom ≫ (α_ G H F).hom =
      ((braiding F G).hom ▷ H) ≫ (α_ G H F).hom ≫ (G ◁ (braiding F H).hom) := by

end

end CategoryTheory.MonoidalCategory.DayConvolution
