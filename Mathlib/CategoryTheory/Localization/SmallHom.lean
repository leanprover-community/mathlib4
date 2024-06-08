/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.Logic.Small.Defs

/-!
# Shrinking morphisms in localized categories

-/

universe w w' w'' v u u' u''

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section

/-- The bijection `(X ⟶ Y) ≃ (X' ⟶ Y')` that is induced by isomorphisms
`e : X ≅ X'` and `e' : Y ≅ Y'`. -/
@[simps]
def homEquivOfIsos {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    (X ⟶ Y) ≃ (X' ⟶ Y') where
  toFun f := e.inv ≫ f ≫ e'.hom
  invFun g := e.hom ≫ g ≫ e'.inv
  left_inv := by aesop_cat
  right_inv := by aesop_cat

end

variable (W : MorphismProperty C)
  {D : Type u'} [Category.{w'} D] (L : C ⥤ D) [L.IsLocalization W]
  {D' : Type u''} [Category.{w''} D'] (L' : C ⥤ D') [L'.IsLocalization W] (X Y Z : C)

namespace MorphismProperty

/-- This property holds if the type of morphisms between `X` and `Y`
in the localized category with respect to `W : MorphismProperty C`
is small. -/
class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

/-- Bijection between types of morphisms in two localized categories
for the same class of morphisms `W`. -/
noncomputable def localizationsHomEquiv :
    (L.obj X ⟶ L.obj Y) ≃ (L'.obj X ⟶ L'.obj Y) :=
  (Localization.uniq L L' W).fullyFaithfulFunctor.homEquiv.trans
    (homEquivOfIsos ((Localization.compUniqFunctor L L' W).app X)
      ((Localization.compUniqFunctor L L' W).app Y))

lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  let e := localizationsHomEquiv W W.Q L X Y
  constructor
  · intro h
    have := h.small
    exact small_map e.symm
  · intro h
    exact ⟨small_map e⟩

lemma hasSmallLocalizedHom_of_isLocalization :
    HasSmallLocalizedHom.{w'} W X Y := by
  rw [W.hasSmallLocalizedHom_iff L]
  infer_instance

lemma small_of_hasSmallLocalizedHom [HasSmallLocalizedHom.{w} W X Y] :
    Small.{w} (L.obj X ⟶ L.obj Y) := by
  rwa [← W.hasSmallLocalizedHom_iff]

variable {X Y} in
lemma hasSmallLocalizedHom_iff_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y' := by
  simp only [W.hasSmallLocalizedHom_iff W.Q]
  exact small_congr (homEquivOfIsos (W.Q.mapIso e) (W.Q.mapIso e'))

end MorphismProperty

namespace Localization

open MorphismProperty

/-- The type of morphisms from `X` to `Y` in the localized category
with respect to `W : MorphismProperty C` that is shrunk to `Type w`
when `HasSmallLocalizedHom.{w} W X Y` holds. -/
def SmallHom [HasSmallLocalizedHom.{w} W X Y] : Type w :=
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  Shrink.{w} (W.Q.obj X ⟶ W.Q.obj Y)

namespace SmallHom

/-- The canonical bijection `SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)`
when `L` is a localization functor for `W : MorphismProperty C` and
that `HasSmallLocalizedHom.{w} W X Y` holds. -/
noncomputable def equiv [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y) :=
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  (equivShrink _).symm.trans (W.localizationsHomEquiv _ _ _ _)

end SmallHom

end Localization

end CategoryTheory
