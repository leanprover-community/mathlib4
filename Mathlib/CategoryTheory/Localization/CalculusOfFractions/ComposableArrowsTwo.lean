/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Essential surjectivity of the functor induced on tuples of composable arrows

Assuming that `L : C ⥤ D` is a localization functor for a class of morphisms `W`
that has both calculs of left and right fractions, we show in this file
that the functor `L.mapComposableArrows 2 : ComposableArrows C 2 ⥤ ComposableArrows D 2`
is essentially surjective.

-/

namespace CategoryTheory

open Category

namespace Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]
  [L.IsLocalization W]

lemma essSurj_mapComposableArrows_two : EssSurj (L.mapComposableArrows 2) where
  mem_essImage Y := by
    obtain ⟨Y₀, Y₁, Y₂, f, g, rfl⟩ := ComposableArrows.mk₂_surjective Y
    have := essSurj L W
    obtain ⟨f', hf'⟩ := exists_rightFraction L W
      ((L.objObjPreimageIso Y₀).hom ≫ f ≫ (L.objObjPreimageIso Y₁).inv)
    obtain ⟨g', hg'⟩ := exists_leftFraction L W
      ((L.objObjPreimageIso Y₁).hom ≫ g ≫ (L.objObjPreimageIso Y₂).inv)
    refine' ⟨ComposableArrows.mk₂ f'.f g'.f,
      ⟨ComposableArrows.isoMk₂
        (Localization.isoOfHom L W f'.s f'.hs ≪≫ L.objObjPreimageIso Y₀)
        (L.objObjPreimageIso Y₁)
        ((Localization.isoOfHom L W g'.s g'.hs).symm ≪≫ (L.objObjPreimageIso Y₂)) ?_ ?_⟩⟩
    · dsimp
      rw [← cancel_mono (L.objObjPreimageIso Y₁).inv, assoc, assoc, assoc, hf',
        Iso.hom_inv_id, comp_id, MorphismProperty.RightFraction.map_s_comp_map]
    · dsimp
      rw [← cancel_mono (L.objObjPreimageIso Y₂).inv, assoc, assoc, assoc, hg',
        Iso.hom_inv_id, comp_id, IsIso.comp_inv_eq,
        MorphismProperty.LeftFraction.map_comp_map_s]

end Localization

end CategoryTheory
