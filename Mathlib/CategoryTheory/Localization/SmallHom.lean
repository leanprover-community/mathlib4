/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Logic.Small.Defs

/-!
# Shrinking morphisms in localized categories

Given a class of morphisms `W : MorphismProperty C`, and two objects `X` and `Y`,
we introduce a type-class `HasSmallLocalizedHom.{w} W X Y` which expresses
that in the localized category with respect to `W`, the type of morphisms from `X`
to `Y` is `w`-small for a certain universe `w`. Under this assumption,
we define `SmallHom.{w} W X Y : Type w` as the shrunk type. For any localization
functor `L : C ⥤ D` for `W`, we provide a bijection
`SmallHom.equiv.{w} W L : SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)` that is compatible
with the composition of morphisms.

-/

universe w w' w'' v u u' u''

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {D : Type u'} [Category.{w'} D] (L : C ⥤ D) [L.IsLocalization W]
  {D' : Type u''} [Category.{w''} D'] (L' : C ⥤ D') [L'.IsLocalization W] (X Y Z : C)

namespace MorphismProperty

/-- This property holds if the type of morphisms between `X` and `Y`
in the localized category with respect to `W : MorphismProperty C`
is small. -/
class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

variable {X Y Z}

/-- Bijection between types of morphisms in two localized categories
for the same class of morphisms `W`. -/
noncomputable def localizationsHomEquiv :
    (L.obj X ⟶ L.obj Y) ≃ (L'.obj X ⟶ L'.obj Y) :=
  (Localization.uniq L L' W).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homEquiv ((Localization.compUniqFunctor L L' W).app X)
      ((Localization.compUniqFunctor L L' W).app Y))

@[simp]
lemma localizationHomEquiv_refl :
    localizationsHomEquiv W L L (X := X) (Y := Y) = Equiv.refl _ := by
  ext f
  simp [localizationsHomEquiv, Localization.compUniqFunctor_eq L L W (𝟭 _) L.rightUnitor]

lemma localizationHomEquiv_comp (f : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    localizationsHomEquiv W L L' (f ≫ g) =
      localizationsHomEquiv W L L' f ≫ localizationsHomEquiv W L L' g := by
  simp [localizationsHomEquiv]

lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  constructor
  · intro h
    have := h.small
    exact small_map (localizationsHomEquiv W W.Q L).symm
  · intro h
    exact ⟨small_map (localizationsHomEquiv W W.Q L)⟩

lemma hasSmallLocalizedHom_of_isLocalization :
    HasSmallLocalizedHom.{w'} W X Y := by
  rw [W.hasSmallLocalizedHom_iff L]
  infer_instance

variable (X Y) in
lemma small_of_hasSmallLocalizedHom [HasSmallLocalizedHom.{w} W X Y] :
    Small.{w} (L.obj X ⟶ L.obj Y) := by
  rwa [← W.hasSmallLocalizedHom_iff]

lemma hasSmallLocalizedHom_iff_of_isos {X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    HasSmallLocalizedHom.{w} W X Y ↔ HasSmallLocalizedHom.{w} W X' Y' := by
  simp only [W.hasSmallLocalizedHom_iff W.Q]
  exact small_congr (Iso.homEquiv (W.Q.mapIso e) (W.Q.mapIso e'))

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

variable {X Y Z}

/-- The canonical bijection `SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y)`
when `L` is a localization functor for `W : MorphismProperty C` and
that `HasSmallLocalizedHom.{w} W X Y` holds. -/
noncomputable def equiv [HasSmallLocalizedHom.{w} W X Y] :
    SmallHom.{w} W X Y ≃ (L.obj X ⟶ L.obj Y) :=
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  (equivShrink _).symm.trans (W.localizationsHomEquiv W.Q L)

variable [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W Y Z]
  [HasSmallLocalizedHom.{w} W X Z]

variable {W}

variable (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z)

/-- The composition on `SmallHom W`. -/
noncomputable def comp (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) :
    SmallHom.{w} W X Z :=
  (equiv W W.Q).symm (equiv W W.Q α ≫ equiv W W.Q β)

lemma equiv_comp : equiv W L (α.comp β) = equiv W L α ≫ equiv W L β := by
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q X Y
  letI := small_of_hasSmallLocalizedHom.{w} W W.Q Y Z
  obtain ⟨α, rfl⟩ := (equivShrink _).surjective α
  obtain ⟨β, rfl⟩ := (equivShrink _).surjective β
  dsimp [equiv, comp]
  rw [Equiv.symm_apply_apply]
  erw [(equivShrink _).symm_apply_apply, (equivShrink _).symm_apply_apply]
  rw [← localizationHomEquiv_comp, localizationHomEquiv_refl, Equiv.refl_symm,
    Equiv.refl_apply, Equiv.refl_apply, localizationHomEquiv_comp]

end SmallHom

end Localization

end CategoryTheory
