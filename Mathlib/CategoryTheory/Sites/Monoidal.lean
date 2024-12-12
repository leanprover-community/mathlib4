/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Closed.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Monoidal category structure on categories of sheaves

-/

universe v v' u u'

namespace CategoryTheory

variable {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C)
  {A : Type u} [Category.{v} A] [MonoidalCategory A]

open MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace Presheaf

variable [MonoidalClosed A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

variable {J} in
lemma isSheaf_ihom (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J ((ihom F).obj G) := by
  sorry

end Presheaf

namespace GrothendieckTopology

variable [MonoidalClosed A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

namespace W

variable {J}

lemma whiskerLeft {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A)  :
    J.W (F ◁ g) := by
  intro H h
  have := hg _ (Presheaf.isSheaf_ihom F H h)
  rw [← Function.Bijective.of_comp_iff' (f := MonoidalClosed.curry)
    ((ihom.adjunction _).homEquiv _ _).bijective]
  rw [← Function.Bijective.of_comp_iff (g := MonoidalClosed.curry) _
    ((ihom.adjunction _).homEquiv _ _).bijective] at this
  convert this using 1
  ext α : 1
  dsimp
  rw [curry_natural_left]

lemma whiskerRight [BraidedCategory A]
    {F₁ F₂ : Cᵒᵖ ⥤ A} (f : F₁ ⟶ F₂) (hf : J.W f) (G : Cᵒᵖ ⥤ A) :
    J.W (f ▷ G) :=
  (J.W.arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2
    (hf.whiskerLeft G)

end W

end GrothendieckTopology

end CategoryTheory
