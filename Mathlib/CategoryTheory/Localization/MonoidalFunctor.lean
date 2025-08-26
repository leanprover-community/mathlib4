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

lemma μNatIso_inv_app_app (X Y : C) :
    ((μNatIso L W ε F).inv.app ((L').obj X)).app ((L').obj Y) =
      F.map (Functor.LaxMonoidal.μ L' X Y) ≫ Functor.OplaxMonoidal.δ (L' ⋙ F) X Y := by
  simp [μNatIso, lift₂NatIso, Lifting₂.iso, Lifting₂.iso']
  rfl

@[reassoc]
lemma μNatIso_naturality {X X' Y Y' : LocalizedMonoidal L W ε} (f : X ⟶ X') (g : Y ⟶ Y') :
    (F.map f ⊗ₘ F.map g) ≫ ((μNatIso L W ε F).hom.app X').app Y' =
      ((μNatIso L W ε F).hom.app X).app Y ≫ F.map (f ⊗ₘ g) := by
  have := ((μNatIso L W ε F).hom.app X').naturality g
  simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, Functor.comp_obj,
    whiskeringRight_obj_obj, whiskeringLeft₂_obj_obj_obj_obj_map, curriedTensor_obj_map,
    Functor.comp_map] at this
  rw [← Category.comp_id (F.map f), ← Category.id_comp (F.map g), MonoidalCategory.tensor_comp,
    MonoidalCategory.id_tensorHom, Category.assoc, this]
  have := (μNatIso L W ε F).hom.naturality f
  apply NatTrans.congr_app at this
  simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, Functor.comp_obj,
    whiskeringRight_obj_obj, NatTrans.comp_app, whiskeringLeft₂_obj_obj_obj_map_app,
    curriedTensor_map_app, Functor.comp_map, whiskeringRight_obj_map,
    Functor.whiskerRight_app] at this
  specialize this Y
  rw [MonoidalCategory.tensorHom_id, ← Category.assoc, this]
  rw [Category.assoc, ← F.map_comp]
  congr

lemma μNatIso_associativity_aux (X Y Z : C) :
    ((μNatIso L W ε F).hom.app ((L').obj X ⊗ (L').obj Y)).app ((L').obj Z) =
      (((μNatIso L W ε F).inv.app ((L').obj X)).app ((L').obj Y)) ▷ F.obj ((L').obj Z) ≫
      (α_ _ _ _).hom ≫
      (F.obj ((L').obj X)) ◁ (((μNatIso L W ε F).hom.app ((L').obj Y)).app ((L').obj Z)) ≫
      ((μNatIso L W ε F).hom.app ((L').obj X)).app ((L').obj Y ⊗ (L').obj Z) ≫
      F.map (α_ _ _ _).inv  := by
  simp [μNatIso_inv_app_app, μNatIso_hom_app_app]
  have := ((μNatIso L W ε F).hom.app ((L').obj X)).naturality (Functor.LaxMonoidal.μ L' Y Z)
  simp at this
  change _ = _ ≫ (F.mapIso (Functor.mapIso _ (Functor.Monoidal.μIso L' Y Z))).hom at this
  rw [← Iso.comp_inv_eq] at this
  simp only [Functor.mapIso_inv, μIso_inv, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
    Category.assoc] at this
  change _ ≫ _ ≫ F.map ((L').obj X ◁ _) = _ at this
  rw [← this]
  simp [μNatIso_hom_app_app]
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
  rw [← this]
  simp only [μNatIso_hom_app_app, Functor.comp_obj, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
    μIso_inv, Category.assoc]
  slice_rhs 5 6 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← F.map_comp]
    simp only [δ_μ, Functor.map_id, MonoidalCategory.whiskerLeft_id]
  simp only [Category.id_comp, Category.assoc, ← Functor.comp_obj]
  rw [map_associator' (L' ⋙ F)]
  slice_rhs 2 3 =>
    simp only [Functor.comp_obj]
    rw [← MonoidalCategory.comp_whiskerRight]
    simp only [Functor.comp_obj, δ_μ, id_whiskerRight]
  simp only [Functor.comp_obj, Category.id_comp, Functor.comp_map, Category.assoc, whiskerLeft_δ_μ,
    Category.comp_id, δ_μ]
  congr 2
  simp only [← F.map_comp]
  simp

/--
Monoidal structure on `F`, given that `L ⋙ F` is monoidal, where `L` is a localization functor.
-/
noncomputable def functorCoremonoidalOfComp : F.CoreMonoidal where
  εIso := εIso (L ⋙ F) ≪≫ F.mapIso ε
  μIso X Y := ((μNatIso L W ε F).app X).app Y
  μIso_hom_natural_left f X := NatTrans.congr_app ((μNatIso L W ε F).hom.naturality f) X
  μIso_hom_natural_right X f := ((μNatIso L W ε F).hom.app X).naturality f
  associativity X Y Z := by
    simp only [Functor.comp_obj, whiskeringRight_obj_obj, Iso.app_hom]
    obtain ⟨x, ⟨eX⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨y, ⟨eY⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨z, ⟨eZ⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices ((μNatIso L W ε F).hom.app ((L').obj x)).app ((L').obj y) ▷ F.obj ((L').obj z) ≫
        ((μNatIso L W ε F).hom.app (((L').obj x) ⊗ ((L').obj y))).app ((L').obj z) ≫
          F.map (α_ ((L').obj x) ((L').obj y) ((L').obj z)).hom =
        (α_ (F.obj ((L').obj x)) (F.obj ((L').obj y)) (F.obj ((L').obj z))).hom ≫
          F.obj ((L').obj x) ◁ ((μNatIso L W ε F).hom.app ((L').obj y)).app ((L').obj z) ≫
            ((μNatIso L W ε F).hom.app ((L').obj x)).app (((L').obj y) ⊗ ((L').obj z)) by
      refine Eq.trans ?_ ((((F.map eX.inv ⊗ₘ F.map eY.inv) ⊗ₘ F.map eZ.inv) ≫= this =≫
        (F.map (eX.hom ⊗ₘ eY.hom ⊗ₘ eZ.hom))).trans ?_)
      · simp only [Category.assoc]
        rw [← F.map_comp, ← associator_naturality, F.map_comp, ← μNatIso_naturality_assoc]
        rw [← Category.comp_id (F.map eZ.inv), ← Category.id_comp (F.map eX.inv ⊗ₘ F.map eY.inv)]
        rw [MonoidalCategory.tensor_comp, MonoidalCategory.tensorHom_id]
        simp only [MonoidalCategory.id_tensorHom, whiskeringLeft₂_obj_obj_obj_obj_obj,
          curriedTensor_obj_obj, Functor.comp_obj, whiskeringRight_obj_obj, Category.assoc]
        rw [← comp_whiskerRight_assoc, μNatIso_naturality]
        rw [MonoidalCategory.whisker_exchange_assoc]
        simp only [← Category.assoc]
        congr 2
        simp only [← MonoidalCategory.tensorHom_id, whiskeringLeft₂_obj_obj_obj_obj_obj,
          curriedTensor_obj_obj, Functor.comp_obj, whiskeringRight_obj_obj, ←
          MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensor_comp, Category.comp_id,
          Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
        simp
      · simp only [associator_conjugation, whiskeringLeft₂_obj_obj_obj_obj_obj,
          curriedTensor_obj_obj, Functor.comp_obj, whiskeringRight_obj_obj, Category.assoc,
          Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
        rw [← μNatIso_naturality, ← MonoidalCategory.id_tensorHom, ← Functor.map_id]
        simp only [Functor.comp_obj, whiskeringRight_obj_obj, curriedTensor_obj_obj,
          ← MonoidalCategory.tensor_comp_assoc, ← Functor.map_comp, Category.id_comp,
          Iso.inv_hom_id]
        rw [μNatIso_naturality_assoc]
        simp only [Functor.map_id, whiskeringRight_obj_obj, Functor.comp_obj, curriedTensor_obj_obj,
          MonoidalCategory.id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc]
        slice_lhs 2 3 =>
          rw [← MonoidalCategory.whiskerLeft_comp, ← Functor.map_comp,
            ← MonoidalCategory.tensor_comp]
          simp only [Iso.inv_hom_id, MonoidalCategory.tensorHom_id, id_whiskerRight, Functor.map_id,
            MonoidalCategory.whiskerLeft_id]
        simp
    simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, Functor.comp_obj,
      whiskeringRight_obj_obj, μNatIso_hom_app_app, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      comp_whiskerRight, Category.assoc, MonoidalCategory.whiskerLeft_comp]
    rw [μNatIso_associativity_aux]
    simp only [Functor.comp_obj, whiskeringRight_obj_obj, whiskeringLeft₂_obj_obj_obj_obj_obj,
      curriedTensor_obj_obj, μNatIso_inv_app_app, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      comp_whiskerRight, μNatIso_hom_app_app, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, Iso.map_inv_hom_id, Category.comp_id]
    simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
      Category.comp_id, ← MonoidalCategory.tensor_comp_assoc, map_δ_μ_assoc, μ_δ, Functor.comp_obj]
    simp
  left_unitality X := by
    obtain ⟨x, ⟨eX⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    simp only [Functor.comp_obj, Iso.trans_hom, εIso_hom, Functor.mapIso_hom, comp_whiskerRight,
      whiskeringRight_obj_obj, Iso.app_hom, Category.assoc]
    suffices (λ_ (F.obj ((L').obj x))).hom = Functor.LaxMonoidal.ε (L ⋙ F) ▷ F.obj ((L').obj x) ≫
        F.map ε.hom ▷ F.obj ((L').obj x) ≫ ((μNatIso L W ε F).hom.app (𝟙_ _)).app ((L').obj x) ≫
          F.map (λ_ ((L').obj x)).hom by
      refine Eq.trans ?_ (((_ ◁ F.map eX.inv) ≫= this =≫ (F.map eX.hom)).trans ?_)
      · simp
      · simp only [id_whiskerLeft, Functor.comp_obj, whiskeringRight_obj_obj,
          curriedTensor_obj_obj, Functor.LaxMonoidal.left_unitality,
          Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, Functor.map_comp, Category.assoc]
        slice_lhs 5 6 =>
          rw [← MonoidalCategory.tensorHom_id, ← Functor.map_id]
          change _ ≫ ((μNatIso L W ε F).hom.app unit).app _
          rw [μNatIso_naturality, μNatIso_hom_app_app']
        simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, Functor.comp_obj,
          whiskeringRight_obj_obj, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
          MonoidalCategory.tensorHom_id, Category.assoc, ← Functor.map_comp]
        have : Functor.LaxMonoidal.ε L' = ε.inv := rfl
        rw [this, ← MonoidalCategory.comp_whiskerRight_assoc]
        simp only [Iso.hom_inv_id, id_whiskerRight, Category.id_comp, δ_μ_assoc, Functor.map_comp]
        slice_rhs 2 3 =>
          rw [← MonoidalCategory.tensorHom_id, ← Functor.map_id, μNatIso_naturality]
        rw [@leftUnitor_inv_naturality_assoc]
        rw [Iso.hom_inv_id_assoc, MonoidalCategory.whisker_exchange_assoc]
        congr 1
        rw [← cancel_epi ((F.obj (L.obj (𝟙_ C))) ◁ F.map eX.hom)]
        conv_rhs => rw [← MonoidalCategory.id_tensorHom, ← Functor.map_id, ← Category.assoc,
          μNatIso_naturality_assoc]
        rw [μNatIso_hom_app_app']
        simp only [whiskeringRight_obj_obj, Functor.comp_obj, curriedTensor_obj_obj,
          Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.id_tensorHom,
          MonoidalCategory.tensorHom_id, Category.assoc]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← Functor.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, MonoidalCategory.whiskerLeft_id,
          Category.id_comp, ← Functor.map_comp]
        congr 2
        rw [MonoidalCategory.whisker_exchange_assoc]
        rw [@leftUnitor_naturality]
        rw [@leftUnitor_hom_app, ε']
        slice_rhs 2 3 =>
          rw [← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id, whiskerRight_id]
        simp only [Category.id_comp, Category.assoc]
        change _ = _ ≫ Functor.LaxMonoidal.μ L' _ _ ≫ _
        simp
    change (λ_ ((L' ⋙ F).obj x)).hom = _
    rw [Functor.LaxMonoidal.left_unitality (L' ⋙ F)]
    simp only [Functor.comp_obj, Functor.comp_map, whiskeringRight_obj_obj, curriedTensor_obj_obj,
      Functor.LaxMonoidal.left_unitality, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal]
    slice_rhs 2 4 =>
      rw [← MonoidalCategory.tensorHom_id, ← Functor.map_id]
      change _ ≫ ((μNatIso L W ε F).hom.app unit).app _
      rw [μNatIso_naturality]
    rw [μNatIso_hom_app_app']
    simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, Functor.comp_obj,
      whiskeringRight_obj_obj, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      MonoidalCategory.tensorHom_id, Category.assoc, ← Functor.map_comp]
    congr
    rw [← Functor.LaxMonoidal.left_unitality L', leftUnitor_hom_app]
    simp only [ε', hom_inv_whiskerRight_assoc]
    change _ = _ ≫ Functor.LaxMonoidal.μ L' _ _ ≫ _
    simp
  right_unitality X := by
    obtain ⟨x, ⟨eX⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    simp only [Functor.comp_obj, Iso.trans_hom, εIso_hom, Functor.mapIso_hom,
      MonoidalCategory.whiskerLeft_comp, whiskeringRight_obj_obj, Iso.app_hom, Category.assoc]
    suffices (ρ_ (F.obj ((L').obj x))).hom = (F.obj ((L').obj x) ◁ Functor.LaxMonoidal.ε (L ⋙ F)) ≫
        (F.obj ((L').obj x) ◁ F.map ε.hom) ≫ ((μNatIso L W ε F).hom.app ((L').obj x)).app (𝟙_ _) ≫
          F.map (ρ_ ((L').obj x)).hom by
      refine Eq.trans ?_ (((F.map eX.inv ▷ _) ≫= this =≫ (F.map eX.hom)).trans ?_)
      · simp
      · simp only [MonoidalCategory.whiskerRight_id, Functor.comp_obj, whiskeringRight_obj_obj,
        curriedTensor_obj_obj, Functor.LaxMonoidal.right_unitality,
        Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, Functor.map_comp, Category.assoc]
        slice_lhs 5 6 =>
          rw [← MonoidalCategory.id_tensorHom, ← Functor.map_id]
          change _ ≫ ((μNatIso L W ε F).hom.app _).app unit
          rw [μNatIso_naturality, μNatIso_hom_app_app'']
        simp only [whiskeringLeft₂_obj_obj_obj_obj_obj, curriedTensor_obj_obj, Functor.comp_obj,
          whiskeringRight_obj_obj, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
          MonoidalCategory.id_tensorHom, Category.assoc, ← Functor.map_comp]
        have : Functor.LaxMonoidal.ε L' = ε.inv := rfl
        rw [this, ← MonoidalCategory.whiskerLeft_comp_assoc]
        simp only [Iso.hom_inv_id, Functor.map_comp]
        slice_rhs 2 3 =>
          rw [← MonoidalCategory.id_tensorHom, ← Functor.map_id, μNatIso_naturality]
        rw [@rightUnitor_inv_naturality_assoc]
        rw [Iso.hom_inv_id_assoc, ← MonoidalCategory.whisker_exchange_assoc]
        congr 1
        rw [← cancel_epi (F.map eX.hom ▷ (F.obj (L.obj (𝟙_ C))))]
        conv_rhs => rw [← MonoidalCategory.tensorHom_id, ← Functor.map_id, ← Category.assoc,
          μNatIso_naturality_assoc]
        rw [μNatIso_hom_app_app'']
        simp only [whiskeringRight_obj_obj, Functor.comp_obj, curriedTensor_obj_obj,
          Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.id_tensorHom,
          MonoidalCategory.tensorHom_id, Category.assoc]
        rw [← MonoidalCategory.comp_whiskerRight_assoc, ← Functor.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, id_whiskerRight, MonoidalCategory.whiskerLeft_id,
          ← Functor.map_comp, Category.id_comp]
        congr 2
        rw [← MonoidalCategory.whisker_exchange_assoc]
        rw [@rightUnitor_naturality]
        rw [@rightUnitor_hom_app, ε']
        slice_rhs 2 3 =>
          rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id]
        simp only [Category.assoc]
        rfl
    change (ρ_ ((L' ⋙ F).obj x)).hom = _
    rw [Functor.LaxMonoidal.right_unitality (L' ⋙ F)]
    simp only [Functor.comp_obj, Functor.comp_map, whiskeringRight_obj_obj, curriedTensor_obj_obj,
      Functor.LaxMonoidal.right_unitality, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.map_comp]
    slice_rhs 2 4 =>
      rw [← MonoidalCategory.id_tensorHom, ← Functor.map_id]
      change _ ≫ ((μNatIso L W ε F).hom.app _).app unit ≫ _
      rw [μNatIso_naturality_assoc, μNatIso_hom_app_app'']
    simp only [whiskeringRight_obj_obj, Functor.comp_obj, curriedTensor_obj_obj,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.id_tensorHom, ←
      Functor.map_comp, Category.assoc]
    congr
    rw [← Functor.LaxMonoidal.right_unitality L', rightUnitor_hom_app]
    simp only [ε', whiskerLeft_hom_inv_assoc]
    change _ = _ ≫ Functor.LaxMonoidal.μ L' _ _ ≫ _
    simp

/--
Monoidal structure on `F`, given that `L ⋙ F` is monoidal, where `L` is a localization functor.
-/
noncomputable def functorMonoidalOfComp : F.Monoidal :=
  (functorCoremonoidalOfComp L W ε F).toMonoidal

end CategoryTheory.Localization.Monoidal
