/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi
import Mathlib.CategoryTheory.Localization.Monoidal
import Mathlib.Combinatorics.Quiver.ReflQuiver
/-!

# Universal property of localized monoidal categories

This file proves that, given a localization functor `L : C ⥤ D`, such that `C` is a monoidal
category, and a functor `F : D ⥤ E` to a monoidal category, such that `L ⋙ F` is monoidal,
then `F` is monoidal with respect to the localized monoidal structure on `D`. See
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`.
-/

universe u

namespace CategoryTheory

open CategoryTheory Limits Opposite MonoidalCategory Functor Functor.Monoidal

namespace Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

variable {E : Type*} [Category E] [MonoidalCategory E] (F : LocalizedMonoidal L W ε ⥤ E)
    [(L ⋙ F).Monoidal]

instance : (L' ⋙ F).Monoidal := inferInstanceAs (L ⋙ F).Monoidal

noncomputable instance : Lifting₂ L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C E).obj (L' ⋙ F))
    (curriedTensor _ ⋙ (whiskeringRight _ _ _).obj F) := by
  change (Lifting₂ L' L' W W
    (((curriedTensor C) ⋙ (whiskeringRight C C D).obj L') ⋙ (whiskeringRight C D E).obj _)
    (tensorBifunctor L W ε ⋙ (whiskeringRight _ _ _).obj F))
  apply (config := {allowSynthFailures := true}) Lifting₂.compRight
  exact inferInstanceAs (Lifting₂ L L W W (curriedTensor C ⋙ (whiskeringRight C C D).obj L')
    (Localization.lift₂ _ (isInvertedBy₂ L W ε) L L))

noncomputable instance : Lifting₂ L' L' W W
    ((((whiskeringLeft₂ _).obj (L' ⋙ F)).obj (L' ⋙ F)).obj (curriedTensor E))
    ((((whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor E)) where
  iso' := Iso.refl _

-- curriedTensorPre F ≅ curriedTensorPost F
/--
The natural isomorphism of bifunctors `F - ⊗ F - ≅ F (- ⊗ -)`, given that `L ⋙ F` is monoidal.
-/
noncomputable def μNatIso : ((((whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor E)) ≅
    (curriedTensor _ ⋙ (whiskeringRight _ _ _).obj F) := by
  refine lift₂NatIso L' L' W W
    ((((whiskeringLeft₂ _).obj (L' ⋙ F)).obj (L' ⋙ F)).obj (curriedTensor E))
    ((curriedTensor C) ⋙ (whiskeringRight C C E).obj (L' ⋙ F))
    ((((whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor E))
    (curriedTensor _ ⋙ (whiskeringRight _ _ _).obj F)
    ?_
  refine NatIso.ofComponents (fun _ ↦ (NatIso.ofComponents (fun _ ↦ μIso (L' ⋙ F) _ _) ?_)) ?_
  · intros
    simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.comp_obj, curriedTensor_obj_obj,
      whiskeringRight_obj_obj, whiskeringLeft₂_obj_obj_obj_obj_map, Functor.comp_map,
      curriedTensor_obj_map, μIso_hom]
    change _ =  _ ≫ (L' ⋙ F).map _
    rw [map_whiskerLeft]
    simp
  · intros
    ext
    simp only [Functor.comp_obj, whiskeringRight_obj_obj, curriedTensor_obj_obj,
      whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.comp_map, whiskeringRight_obj_map,
      NatTrans.comp_app, Functor.whiskerRight_app, curriedTensor_map_app,
      NatIso.ofComponents_hom_app, whiskeringLeft₂_obj_obj_obj_map_app]
    change _ = _ ≫ (L' ⋙ F).map _
    rw [map_whiskerRight]
    simp

lemma μNatIso_hom_app_app (X Y : C) :
    ((μNatIso L W ε F).hom.app ((L').obj X)).app ((L').obj Y) =
      Functor.LaxMonoidal.μ (L' ⋙ F) X Y ≫
        F.map (Functor.OplaxMonoidal.δ L' X Y) := by
  simp [μNatIso, lift₂NatIso, Lifting₂.iso, Lifting₂.iso']
  rfl

/--
Variant of `μNatIso_hom_app_app` where the notation `L'` in the first argument is replaced by `L`
-/
lemma μNatIso_hom_app_app' (X Y : C) :
  ((μNatIso L W ε F).hom.app (L.obj X)).app ((L').obj Y) =
    Functor.LaxMonoidal.μ (L ⋙ F) X Y ≫
      F.map (Functor.OplaxMonoidal.δ L' X Y) :=
  μNatIso_hom_app_app _ _ _ _ X Y

/--
Variant of `μNatIso_hom_app_app` where the notation `L'` in the second argument is replaced by `L`
-/
lemma μNatIso_hom_app_app'' (X Y : C) :
  ((μNatIso L W ε F).hom.app ((L').obj X)).app (L.obj Y) =
    Functor.LaxMonoidal.μ (L ⋙ F) X Y ≫
      F.map (Functor.OplaxMonoidal.δ L' X Y) :=
  μNatIso_hom_app_app _ _ _ _ X Y

/--
Monoidal structure on `F`, given that `L ⋙ F` is monoidal, where `L` is a localization functor.
-/
noncomputable def functorCoremonoidalOfComp : F.CoreMonoidal := by
  refine Functor.CoreMonoidal.ofBifunctor (εIso (L ⋙ F) ≪≫ F.mapIso ε) (μNatIso L W ε F) ?_ ?_ ?_
  · apply natTrans₃_ext (L') (L') (L') W W W
    intro X Y Z
    simp only [curriedTensorPrePre_obj_obj_obj, curriedTensorPostPost'_obj_obj_obj,
      LaxMonoidal.firstMap_app_app_app, LaxMonoidal.secondMap_app_app_app]
    simp only [μNatIso_hom_app_app, comp_obj, CoreMonoidal.toMonoidal_toOplaxMonoidal,
      comp_whiskerRight, Category.assoc, MonoidalCategory.whiskerLeft_comp]
    have := (μNatIso L W ε F).hom.naturality ((Functor.LaxMonoidal.μ L' X Y))
    apply NatTrans.congr_app at this
    specialize this ((L').obj Z)
    simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, Functor.comp_obj,
      whiskeringRight_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, NatTrans.comp_app,
      whiskeringLeft₂_obj_obj_obj_map_app, curriedTensor_map_app, Functor.comp_map,
      whiskeringRight_obj_map, Functor.whiskerRight_app] at this
    change _ = _ ≫ (F.mapIso ((Functor.mapIso _ (Functor.Monoidal.μIso L' _ _)).app _)).hom at this
    rw [← Iso.comp_inv_eq] at this
    simp only [Functor.mapIso_inv, Iso.app_inv, Category.assoc] at this
    change _ ≫ _ ≫ F.map (_ ▷ (L').obj Z) = _ at this
    rw [← this, μNatIso_hom_app_app]
    simp only [comp_obj, CoreMonoidal.toMonoidal_toOplaxMonoidal, μIso_inv, Category.assoc]
    have := ((μNatIso L W ε F).hom.app ((L').obj X)).naturality (Functor.LaxMonoidal.μ L' Y Z)
    simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, comp_obj,
      whiskeringRight_obj_obj, CoreMonoidal.toMonoidal_toLaxMonoidal,
      whiskeringLeft₂_obj_obj_obj_obj_map, curriedTensor_obj_map, Functor.comp_map] at this
    change _ = _ ≫ (F.mapIso (Functor.mapIso _ (Functor.Monoidal.μIso L' Y Z))).hom at this
    rw [← Iso.comp_inv_eq] at this
    simp only [Functor.mapIso_inv, μIso_inv, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Category.assoc] at this
    change _ ≫ _ ≫ F.map ((L').obj X ◁ _) = _ at this
    rw [← this]
    simp only [μNatIso_hom_app_app, comp_obj, CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Category.assoc]
    simp only [← map_comp, OplaxMonoidal.associativity]
    simp only [← Category.assoc, map_comp]
    congr 2
    simp only [Category.assoc]
    simp only [← comp_whiskerRight_assoc, map_δ_μ, id_whiskerRight, Category.id_comp,
      ← MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_id]
    exact Functor.Monoidal.toLaxMonoidal.associativity (F := L' ⋙ F) _ _ _
  · apply natTrans_ext (L') W
    intro X
    simp only [comp_obj, curriedTensor_obj_obj, LaxMonoidal.leftMapₗ_app, Iso.trans_hom, εIso_hom,
      mapIso_hom, NatTrans.comp_app, curriedTensorPre_obj_obj, LaxMonoidal.topMapₗ_app,
      comp_whiskerRight, curriedTensorPost_obj_obj, LaxMonoidal.bottomMapₗ_app,
      LaxMonoidal.left_unitality, CoreMonoidal.toMonoidal_toLaxMonoidal, map_comp, Category.assoc]
    change _ = _ ≫ _ ≫ ((μNatIso L W ε F).hom.app unit).app _ ≫ _ ≫ _
    have := NatTrans.congr_app ((μNatIso L W ε F).hom.naturality ε.hom) ((L').obj X)
    simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, comp_obj,
      whiskeringRight_obj_obj, NatTrans.comp_app, whiskeringLeft₂_obj_obj_obj_map_app,
      curriedTensor_map_app, Functor.comp_map, whiskeringRight_obj_map, whiskerRight_app] at this
    slice_rhs 2 3 => rw [this]
    simp only [comp_obj, whiskeringRight_obj_obj, curriedTensor_obj_obj, μNatIso_hom_app_app',
      CoreMonoidal.toMonoidal_toOplaxMonoidal, Category.assoc]
    change (λ_ ((L' ⋙ F).obj _)).hom = _
    rw [Functor.LaxMonoidal.left_unitality (L' ⋙ F), show LaxMonoidal.ε L' = ε.inv from rfl]
    simp [← Functor.map_comp]
    rfl
  · apply natTrans_ext (L') W
    intro X
    simp only [comp_obj, flip_obj_obj, curriedTensor_obj_obj, LaxMonoidal.leftMapᵣ_app,
      Iso.trans_hom, εIso_hom, mapIso_hom, flipFunctor_obj, NatTrans.comp_app,
      curriedTensorPre_obj_obj, LaxMonoidal.topMapᵣ_app, MonoidalCategory.whiskerLeft_comp,
      curriedTensorPost_obj_obj, flipFunctor_map_app_app, LaxMonoidal.bottomMapᵣ_app,
      LaxMonoidal.right_unitality, CoreMonoidal.toMonoidal_toLaxMonoidal, map_comp, Category.assoc]
    change _ = _ ≫ _ ≫ ((μNatIso L W ε F).hom.app _).app unit ≫ _ ≫ _
    have := ((μNatIso L W ε F).hom.app ((L').obj X)).naturality ε.hom
    simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, comp_obj,
      whiskeringRight_obj_obj, whiskeringLeft₂_obj_obj_obj_obj_map, curriedTensor_obj_map,
      Functor.comp_map] at this
    slice_rhs 2 3 => rw [this]
    simp only [comp_obj, whiskeringRight_obj_obj, curriedTensor_obj_obj, μNatIso_hom_app_app'',
      CoreMonoidal.toMonoidal_toOplaxMonoidal, Category.assoc]
    change (ρ_ ((L' ⋙ F).obj _)).hom = _
    rw [Functor.LaxMonoidal.right_unitality (L' ⋙ F), show LaxMonoidal.ε L' = ε.inv from rfl]
    simp [← Functor.map_comp]
    rfl

/--
Monoidal structure on `F`, given that `L ⋙ F` is monoidal, where `L` is a localization functor.
-/
noncomputable def functorMonoidalOfComp : F.Monoidal :=
  (functorCoremonoidalOfComp L W ε F).toMonoidal

end CategoryTheory.Localization.Monoidal
