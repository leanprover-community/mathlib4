/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution

/-!
# Braidings for Day convolution

In this file, we show that if `C` is a braided monoidal category and
`V` also a braided monoidal category, then the Day convolution monoidal structure
on `C ⥤ V` is also braided monoidal. We prove it by constructing an explicit
braiding isomorphism whenever sufficient Day convolutions exist, and we
prove that it satisfies the forward and reverse hexagon identities.

Furthermore, we show that when both `C` and `V` are symmetric monoidal
categories, then the Day convolution monoidal structure is symmetric as well.
-/

@[expose] public section

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

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `F ⊠ G ⟶ (tensor C) ⋙ (G ⊛ F)` that corepresents
the braiding morphism `F ⊛ G ⟶ G ⊛ F`. -/
@[simps]
def braidingHomCorepresenting : F ⊠ G ⟶ tensor C ⋙ G ⊛ F where
  app _ := (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (G ⊛ F).map (β_ _ _).hom
  naturality {x y} f := by simp [tensorHom_def, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `F ⊠ G ⟶ (tensor C) ⋙ (G ⊛ F)` that corepresents
the braiding morphism `F ⊛ G ⟶ G ⊛ F`. -/
@[simps]
def braidingInvCorepresenting : G ⊠ F ⟶ tensor C ⋙ F ⊛ G where
  app _ := (β_ _ _).inv ≫ (unit F G).app (_, _) ≫ (F ⊛ G).map (β_ _ _).inv
  naturality {x y} f := by simp [tensorHom_def, ← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The braiding isomorphism for Day convolution. -/
def braiding : F ⊛ G ≅ G ⊛ F where
  hom := corepresentableBy F G |>.homEquiv.symm <| braidingHomCorepresenting F G
  inv := corepresentableBy G F |>.homEquiv.symm <| braidingInvCorepresenting F G
  hom_inv_id := by
    apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ G) (unit F G)
    ext
    simp [-tensor_obj]
  inv_hom_id := by
    apply Functor.hom_ext_of_isLeftKanExtension (G ⊛ F) (unit G F)
    ext
    simp [-tensor_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma unit_app_braiding_hom_app (x y : C) :
    (unit F G).app (x, y) ≫ (braiding F G).hom.app (x ⊗ y) =
    (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (G ⊛ F).map (β_ _ _).hom := by
  change
    (unit F G).app (x, y) ≫ (braiding F G).hom.app ((tensor C).obj (x, y)) = _
  simp [braiding, braidingHomCorepresenting, -tensor_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma unit_app_braiding_inv_app (x y : C) :
    (unit G F).app (x, y) ≫ (braiding F G).inv.app (x ⊗ y) =
    (β_ _ _).inv ≫ (unit F G).app (_, _) ≫ (F ⊛ G).map (β_ _ _).inv := by
  change
    (unit G F).app (x, y) ≫ (braiding F G).inv.app ((tensor C).obj (x, y)) = _
  simp [braiding, braidingHomCorepresenting, -tensor_obj]

end

variable {F G}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma braiding_naturality_right (H : C ⥤ V) (η : F ⟶ G)
    [DayConvolution F H] [DayConvolution H F]
    [DayConvolution G H] [DayConvolution H G] :
    DayConvolution.map (𝟙 H) η ≫ (braiding H G).hom =
    (braiding H F).hom ≫ DayConvolution.map η (𝟙 H) := by
  apply Functor.hom_ext_of_isLeftKanExtension (H ⊛ F) (unit H F)
  ext ⟨_, _⟩
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma braiding_naturality_left (η : F ⟶ G) (H : C ⥤ V)
    [DayConvolution F H] [DayConvolution H F]
    [DayConvolution G H] [DayConvolution H G] :
    DayConvolution.map η (𝟙 H) ≫ (braiding G H).hom =
    (braiding F H).hom ≫ DayConvolution.map (𝟙 H) η := by
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ H) (unit F H)
  ext ⟨_, _⟩
  simp

variable
  [∀ (v : V) (d : C),
    Limits.PreservesColimitsOfShape (CostructuredArrow (tensor C) d) (tensorLeft v)]
  [∀ (v : V) (d : C),
    Limits.PreservesColimitsOfShape (CostructuredArrow (tensor C) d) (tensorRight v)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F G) in
lemma hexagon_forward (H : C ⥤ V)
    [DayConvolution F G] [DayConvolution G H] [DayConvolution F (G ⊛ H)]
    [DayConvolution (F ⊛ G) H] [DayConvolution H F] [DayConvolution G (H ⊛ F)]
    [DayConvolution (G ⊛ H) F] [DayConvolution G F] [DayConvolution (G ⊛ F) H]
    [DayConvolution F H] [DayConvolution G (F ⊛ H)] :
    (associator F G H).hom ≫ (braiding F (G ⊛ H)).hom ≫ (associator G H F).hom =
    (DayConvolution.map (braiding F G).hom (𝟙 H)) ≫ (associator G F H).hom ≫
      (DayConvolution.map (𝟙 G) (braiding F H).hom) := by
  apply Functor.hom_ext_of_isLeftKanExtension ((F ⊛ G) ⊛ H) (unit _ H)
  apply Functor.hom_ext_of_isLeftKanExtension ((F ⊛ G) ⊠ H)
    (ExternalProduct.extensionUnitLeft (F ⊛ G) (unit F G) H)
  ext ⟨⟨x, y⟩, z⟩
  dsimp
  simp only [whiskerLeft_id, Category.comp_id, associator_hom_unit_unit_assoc,
    externalProductBifunctor_obj_obj, tensor_obj, NatTrans.naturality_assoc,
    NatTrans.naturality, unit_app_braiding_hom_app_assoc,
    BraidedCategory.braiding_tensor_left_hom, Functor.map_comp, Category.assoc,
    Iso.map_hom_inv_id, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_right_hom, Iso.map_inv_hom_id_assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, unit_app_map_app_assoc,
    NatTrans.id_app, tensorHom_id]
  simp only [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc,
    unit_app_braiding_hom_app]
  simp only [whiskerLeft_comp, ← Functor.map_comp, Category.assoc,
    Functor.comp_obj, tensor_obj, comp_whiskerRight,
    whiskerRight_comp_unit_app_assoc, NatTrans.naturality_assoc,
    NatTrans.naturality, associator_hom_unit_unit_assoc,
    externalProductBifunctor_obj_obj, unit_app_map_app_assoc, NatTrans.id_app,
    id_tensorHom]
  rw [← BraidedCategory.hexagon_reverse, ← whiskerLeft_comp_assoc]
  haveI := unit_app_braiding_hom_app F H x z =≫ (H ⊛ F).map (β_ z x).inv
  dsimp at this
  simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id] at this
  rw [← this, whiskerLeft_comp_assoc]
  simp [← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F G) in
lemma hexagon_reverse (H : C ⥤ V)
    [DayConvolution F G] [DayConvolution G H] [DayConvolution F (G ⊛ H)]
    [DayConvolution (F ⊛ G) H] [DayConvolution H (F ⊛ G)] [DayConvolution H F]
    [DayConvolution (H ⊛ F) G] [DayConvolution H G] [DayConvolution F (H ⊛ G)]
    [DayConvolution F H] [DayConvolution (F ⊛ H) G] :
    (associator F G H).inv ≫ (braiding (F ⊛ G) H).hom ≫ (associator H F G).inv =
    (DayConvolution.map (𝟙 F) (braiding G H).hom) ≫ (associator F H G).inv ≫
      (DayConvolution.map (braiding F H).hom (𝟙 G)) := by
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ G ⊛ H) (unit _ _)
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊠ (G ⊛ H))
    (ExternalProduct.extensionUnitRight (G ⊛ H) (unit G H) F)
  ext ⟨x, y, z⟩
  dsimp
  simp only [whiskerRight_tensor, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id, associator_inv_unit_unit_assoc,
    externalProductBifunctor_obj_obj, tensor_obj, NatTrans.naturality_assoc,
    NatTrans.naturality, unit_app_braiding_hom_app_assoc,
    BraidedCategory.braiding_tensor_right_hom, Functor.map_comp, Category.assoc,
    Iso.map_inv_hom_id, Category.comp_id,
    BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_tensor_left_hom, Iso.map_hom_inv_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, unit_app_map_app_assoc,
    NatTrans.id_app, id_tensorHom]
  simp only [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc,
    unit_app_braiding_hom_app]
  simp only [comp_whiskerRight, ← Functor.map_comp, Category.assoc, Functor.comp_obj, tensor_obj,
    whiskerLeft_comp, whiskerLeft_comp_unit_app_assoc, NatTrans.naturality_assoc,
    NatTrans.naturality, associator_inv_unit_unit_assoc, externalProductBifunctor_obj_obj,
    unit_app_map_app_assoc, NatTrans.id_app, tensorHom_id]
  congr 2
  rw [← BraidedCategory.hexagon_forward, ← comp_whiskerRight_assoc]
  haveI := unit_app_braiding_hom_app F H x z =≫ (H ⊛ F).map (β_ z x).inv
  dsimp at this
  simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id] at this
  rw [← this, comp_whiskerRight_assoc]
  simp [← Functor.map_comp]

end

section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalCategory V] [SymmetricCategory V]
  (F G : C ⥤ V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma symmetry [DayConvolution F G] [DayConvolution G F] :
    (braiding F G).hom ≫ (braiding G F).hom = 𝟙 _ := by
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ G) (unit F G)
  ext ⟨x, y⟩
  simp [← Functor.map_comp]

end

end CategoryTheory.MonoidalCategory.DayConvolution
