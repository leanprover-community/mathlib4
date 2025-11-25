/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Presentable objects and adjunctions

If `adj : F ⊣ G` and `G` is `κ`-accessible for a regular cardinal `κ`,
then `F` preserves `κ`-presentable objects.

Moreover, if `G : D ⥤ C` is fully faithful, then `D` is locally `κ`-presentable
(resp `κ`-accessible) if `C` is.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

namespace Adjunction

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

include adj

lemma isCardinalPresentable_leftAdjoint_obj (X : C) [IsCardinalPresentable X κ]
    [G.IsCardinalAccessible κ] :
    IsCardinalPresentable (F.obj X) κ := by
  rw [isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{v}]
  exact Functor.isCardinalAccessible_of_natIso
    (show G ⋙ _ ≅ _ from (Adjunction.compUliftCoyonedaIso.{0} adj).symm.app (op X)) κ

variable {κ} in
lemma isCardinalFilteredGenerator
    {P : ObjectProperty C} (hP : P.IsCardinalFilteredGenerator κ)
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    (P.map F).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro Y ⟨X, hX, ⟨e⟩⟩
    have hX' := hP.le_isCardinalPresentable X hX
    rw [isCardinalPresentable_iff] at hX' ⊢
    have := adj.isCardinalPresentable_leftAdjoint_obj κ X
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape Y := by
    have := adj.isLeftAdjoint
    obtain ⟨J, _, _, ⟨hY⟩⟩ := hP.exists_colimitsOfShape (G.obj Y)
    exact ⟨J, inferInstance, inferInstance,
      ObjectProperty.prop_of_isIso _ (adj.counit.app Y) ⟨{
        diag := _
        ι := _
        isColimit := isColimitOfPreserves F hY.isColimit
        prop_diag_obj j := P.prop_map_obj _ (hY.prop_diag_obj j) }⟩⟩

lemma hasCardinalFilteredGenerator [HasCardinalFilteredGenerator C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    HasCardinalFilteredGenerator D κ where
  toLocallySmall := locallySmall_of_faithful G
  exists_generator := by
    obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
    exact ⟨P.map F, inferInstance, adj.isCardinalFilteredGenerator hP⟩

lemma isCardinalLocallyPresentable [IsCardinalLocallyPresentable C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    IsCardinalLocallyPresentable D κ where
  toHasColimitsOfSize :=
    letI : Reflective G := ⟨_, adj⟩
    hasColimits_of_reflective G
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ

lemma isCardinalAccessibleCategory [IsCardinalAccessibleCategory C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    IsCardinalAccessibleCategory D κ where
  toHasCardinalFilteredColimits := ⟨fun _ _ _ ↦
    let : Reflective G := ⟨_, adj⟩
    hasColimitsOfShape_of_reflective G⟩
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ

end Adjunction

end CategoryTheory
