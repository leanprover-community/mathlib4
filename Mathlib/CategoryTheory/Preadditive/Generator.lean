/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Generator
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

#align_import category_theory.preadditive.generator from "leanprover-community/mathlib"@"09f981f72d43749f1fa072deade828d9c1e185bb"

/-!
# Separators in preadditive categories

This file contains characterizations of separating sets and objects that are valid in all
preadditive categories.

-/


universe v u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem Preadditive.isSeparating_iff (𝒢 : Set C) :
    IsSeparating 𝒢 ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : G ⟶ X), h ≫ f = 0) → f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.comp_zero] using hf), fun h𝒢 X Y f g hfg =>
                                 -- 🎉 no goals
    sub_eq_zero.1 <| h𝒢 _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩
                              -- 🎉 no goals
#align category_theory.preadditive.is_separating_iff CategoryTheory.Preadditive.isSeparating_iff

theorem Preadditive.isCoseparating_iff (𝒢 : Set C) :
    IsCoseparating 𝒢 ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ G ∈ 𝒢, ∀ (h : Y ⟶ G), f ≫ h = 0) → f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.zero_comp] using hf), fun h𝒢 X Y f g hfg =>
                                 -- 🎉 no goals
    sub_eq_zero.1 <| h𝒢 _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩
                              -- 🎉 no goals
#align category_theory.preadditive.is_coseparating_iff CategoryTheory.Preadditive.isCoseparating_iff

theorem Preadditive.isSeparator_iff (G : C) :
    IsSeparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = 0) → f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.comp_zero] using hf), fun hG =>
                                     -- 🎉 no goals
    (isSeparator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <| hG _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩
                                -- 🎉 no goals
#align category_theory.preadditive.is_separator_iff CategoryTheory.Preadditive.isSeparator_iff

theorem Preadditive.isCoseparator_iff (G : C) :
    IsCoseparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = 0) → f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.zero_comp] using hf), fun hG =>
                                     -- 🎉 no goals
    (isCoseparator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <| hG _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩
                                -- 🎉 no goals
#align category_theory.preadditive.is_coseparator_iff CategoryTheory.Preadditive.isCoseparator_iff

theorem isSeparator_iff_faithful_preadditiveCoyoneda (G : C) :
    IsSeparator G ↔ Faithful (preadditiveCoyoneda.obj (op G)) := by
  rw [isSeparator_iff_faithful_coyoneda_obj, ← whiskering_preadditiveCoyoneda, Functor.comp_obj,
    whiskeringRight_obj_obj]
  exact ⟨fun h => Faithful.of_comp _ (forget AddCommGroupCat), fun h => Faithful.comp _ _⟩
  -- 🎉 no goals
#align category_theory.is_separator_iff_faithful_preadditive_coyoneda CategoryTheory.isSeparator_iff_faithful_preadditiveCoyoneda

theorem isSeparator_iff_faithful_preadditiveCoyonedaObj (G : C) :
    IsSeparator G ↔ Faithful (preadditiveCoyonedaObj (op G)) := by
  rw [isSeparator_iff_faithful_preadditiveCoyoneda, preadditiveCoyoneda_obj]
  -- ⊢ Faithful (preadditiveCoyonedaObj (op G) ⋙ forget₂ (ModuleCat (End (op G))) A …
  exact ⟨fun h => Faithful.of_comp _ (forget₂ _ AddCommGroupCat.{v}), fun h => Faithful.comp _ _⟩
  -- 🎉 no goals
#align category_theory.is_separator_iff_faithful_preadditive_coyoneda_obj CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaObj

theorem isCoseparator_iff_faithful_preadditiveYoneda (G : C) :
    IsCoseparator G ↔ Faithful (preadditiveYoneda.obj G) := by
  rw [isCoseparator_iff_faithful_yoneda_obj, ← whiskering_preadditiveYoneda, Functor.comp_obj,
    whiskeringRight_obj_obj]
  exact ⟨fun h => Faithful.of_comp _ (forget AddCommGroupCat), fun h => Faithful.comp _ _⟩
  -- 🎉 no goals
#align category_theory.is_coseparator_iff_faithful_preadditive_yoneda CategoryTheory.isCoseparator_iff_faithful_preadditiveYoneda

theorem isCoseparator_iff_faithful_preadditiveYonedaObj (G : C) :
    IsCoseparator G ↔ Faithful (preadditiveYonedaObj G) := by
  rw [isCoseparator_iff_faithful_preadditiveYoneda, preadditiveYoneda_obj]
  -- ⊢ Faithful (preadditiveYonedaObj G ⋙ forget₂ (ModuleCat (End G)) AddCommGroupC …
  exact ⟨fun h => Faithful.of_comp _ (forget₂ _ AddCommGroupCat.{v}), fun h => Faithful.comp _ _⟩
  -- 🎉 no goals
#align category_theory.is_coseparator_iff_faithful_preadditive_yoneda_obj CategoryTheory.isCoseparator_iff_faithful_preadditiveYonedaObj

end CategoryTheory
