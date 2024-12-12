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

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {A : Type u} [Category.{v} A] [MonoidalCategory A]

open Opposite Limits MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace Presheaf

variable [MonoidalClosed A]

noncomputable def functorEnrichedHomCoyonedaObjEquiv (M : A) (F G : Cᵒᵖ ⥤ A)
    [HasFunctorEnrichedHom A F G] (X : C) :
    (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op X) ≃
    (presheafHom (F ⊗ (Functor.const _).obj M) G).obj (op X) where
  toFun f :=
    { app := fun j ↦
        MonoidalClosed.uncurry (f ≫ enrichedHomπ A _ _ (Under.mk j.unop.hom.op))
      naturality := sorry }
  invFun g := end_.lift (fun j ↦ MonoidalClosed.curry (g.app (op (Over.mk j.hom.unop)))) (by
    sorry)
  left_inv f := by
    dsimp
    ext j
    dsimp
    simp only [curry_uncurry, end_.lift_π]
    rfl
  right_inv g := by
    dsimp
    ext j
    dsimp
    simp only [uncurry_curry, end_.lift_π]
    rfl

lemma isSheaf_functorEnrichedHom (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G)
    [HasFunctorEnrichedHom A F G] :
    Presheaf.IsSheaf J (functorEnrichedHom A F G) := by
  intro M
  have := functorEnrichedHomCoyonedaObjEquiv M F G
  have := Presheaf.IsSheaf.hom (F ⊗ (Functor.const _).obj M) G hG
  -- introduce `Presheaf.isSheaf_of_nat_equiv`
  sorry

end Presheaf

namespace GrothendieckTopology

variable [MonoidalClosed A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

namespace W

lemma whiskerLeft {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A) :
    J.W (F ◁ g) := fun H h ↦ by
  have := hg _ (Presheaf.isSheaf_functorEnrichedHom F H h)
  rw [← Function.Bijective.of_comp_iff' (f := MonoidalClosed.curry)
    ((ihom.adjunction _).homEquiv _ _).bijective]
  rw [← Function.Bijective.of_comp_iff (g := MonoidalClosed.curry) _
    ((ihom.adjunction _).homEquiv _ _).bijective] at this
  convert this using 1
  ext α : 1
  dsimp
  rw [curry_natural_left]

lemma whiskerRight [BraidedCategory A]
    {F₁ F₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} (hf : J.W f) (G : Cᵒᵖ ⥤ A) :
    J.W (f ▷ G) :=
  (J.W.arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2 (hf.whiskerLeft G)

end W

end GrothendieckTopology

end CategoryTheory
