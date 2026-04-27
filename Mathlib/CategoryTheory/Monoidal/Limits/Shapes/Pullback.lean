/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Tactic.CategoryTheory.SpecializeMap

/-!
# Pullbacks and pushouts in a monoidal category

For numerous simp lemmas of the form `f ≫ g = h`, we add accompanying simp lemmas of the form
`Q ◁ f ≫ Q ◁ g = Q ◁ h` and `f ▷ Q ≫ g ▷ Q = h ▷ Q`. This file and
`Mathlib.CategoryTheory.Monoidal.Limits.HasLimits` are needed to define a monoidal category
structure in `Mathlib.CategoryTheory.Monoidal.Arrow`.

-/

public section

universe v u

open CategoryTheory Limits MonoidalCategory

attribute [specialize_map tensorLeft (suffix := "_tensorLeft")]
  IsPushout.inl_desc
  IsPushout.inr_desc
  IsPushout.inl_isoPushout_inv
  IsPushout.inr_isoPushout_inv
  IsPushout.inl_isoPushout_hom
  IsPushout.inr_isoPushout_hom
  pushout.condition
  inl_comp_pushoutSymmetry_hom
  inr_comp_pushoutSymmetry_hom

attribute [reassoc (attr := simp)]
  IsPushout.inl_desc_tensorLeft
  IsPushout.inr_desc_tensorLeft
  IsPushout.inl_isoPushout_inv_tensorLeft
  IsPushout.inr_isoPushout_inv_tensorLeft
  IsPushout.inl_isoPushout_hom_tensorLeft
  IsPushout.inr_isoPushout_hom_tensorLeft
  inl_comp_pushoutSymmetry_hom_tensorLeft
  inr_comp_pushoutSymmetry_hom_tensorLeft

attribute [reassoc] pushout.condition_tensorLeft

attribute [specialize_map tensorRight (suffix := "_tensorRight")]
  IsPushout.inl_desc
  IsPushout.inr_desc
  IsPushout.inl_isoPushout_inv
  IsPushout.inr_isoPushout_inv
  IsPushout.inl_isoPushout_hom
  IsPushout.inr_isoPushout_hom
  pushout.condition
  inl_comp_pushoutSymmetry_hom
  inr_comp_pushoutSymmetry_hom

attribute [reassoc (attr := simp)]
  IsPushout.inl_desc_tensorRight
  IsPushout.inr_desc_tensorRight
  IsPushout.inl_isoPushout_inv_tensorRight
  IsPushout.inr_isoPushout_inv_tensorRight
  IsPushout.inl_isoPushout_hom_tensorRight
  IsPushout.inr_isoPushout_hom_tensorRight
  inl_comp_pushoutSymmetry_hom_tensorRight
  inr_comp_pushoutSymmetry_hom_tensorRight

attribute [reassoc] pushout.condition_tensorRight

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [HasPushouts C]
  {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) {Q : C}

variable {A B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y}

@[reassoc]
lemma CategoryTheory.MonoidalCategory.Limits.pushout.associator_naturality_left_condition
    {h : Z ⊗ W ⟶ X} : f ▷ Z ▷ W ≫ (α_ B Z W).hom ≫ B ◁ h ≫ pushout.inl (f ▷ X) (A ◁ g) =
      (α_ A Z W).hom ≫ A ◁ (h ≫ g) ≫ pushout.inr (f ▷ X) (A ◁ g) := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, pushout.condition,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

@[reassoc]
lemma CategoryTheory.MonoidalCategory.Limits.pushout.associator_inv_naturality_right_condition
    {h : Z ⊗ W ⟶ A} : Z ◁ W ◁ g ≫ (α_ Z W Y).inv ≫ h ▷ Y ≫ pushout.inr (f ▷ X) (A ◁ g) =
      (α_ Z W X).inv ≫ (h ≫ f) ▷ X ≫ pushout.inl (f ▷ X) (A ◁ g) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← pushout.condition,
    ← comp_whiskerRight_assoc]
