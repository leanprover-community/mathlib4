/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.GroupCat.Preadditive

#align_import category_theory.preadditive.yoneda.basic from "leanprover-community/mathlib"@"09f981f72d43749f1fa072deade828d9c1e185bb"

/-!
# The Yoneda embedding for preadditive categories

The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure.

We also show that this presheaf is additive and that it is compatible with the normal Yoneda
embedding in the expected way and deduce that the preadditive Yoneda embedding is fully faithful.

## TODO
* The Yoneda embedding is additive itself

-/


universe v u

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the `End Y`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (End Y) where
  obj X := ModuleCat.of _ (X.unop ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => f.unop ≫ g
      map_add' := fun g g' => comp_add _ _ _ _ _ _
      map_smul' := fun r g => Eq.symm <| Category.assoc _ _ _ }
#align category_theory.preadditive_yoneda_obj CategoryTheory.preadditiveYonedaObj

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditiveYonedaObj`.
-/
@[simps]
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat.{v} where
  obj Y := preadditiveYonedaObj Y ⋙ forget₂ _ _
  map f :=
    { app := fun X =>
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun g g' => add_comp _ _ _ _ _ _ }
      naturality := fun X X' g => AddCommGroupCat.ext fun x => Category.assoc _ _ _ }
  map_id _ := by ext; dsimp; simp
  map_comp f g := by ext; dsimp; simp
#align category_theory.preadditive_yoneda CategoryTheory.preadditiveYoneda

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveCoyonedaObj (X : Cᵒᵖ) : C ⥤ ModuleCat.{v} (End X) where
  obj Y := ModuleCat.of _ (unop X ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => g ≫ f
      map_add' := fun g g' => add_comp _ _ _ _ _ _
      map_smul' := fun r g => Category.assoc _ _ _ }
#align category_theory.preadditive_coyoneda_obj CategoryTheory.preadditiveCoyonedaObj

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditiveCoyonedaObj`.
-/
@[simps]
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat.{v} where
  obj X := preadditiveCoyonedaObj X ⋙ forget₂ _ _
  map f :=
    { app := fun Y =>
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun g g' => comp_add _ _ _ _ _ _ }
      naturality := fun Y Y' g =>
        AddCommGroupCat.ext fun x => Eq.symm <| Category.assoc _ _ _ }
  map_id _ := by ext; dsimp; simp
  map_comp f g := by ext; dsimp; simp
#align category_theory.preadditive_coyoneda CategoryTheory.preadditiveCoyoneda

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] CategoryTheory.preadditiveYoneda_map_app_apply
  CategoryTheory.preadditiveCoyoneda_map_app_apply

instance additive_yonedaObj (X : C) : Functor.Additive (preadditiveYonedaObj X) where
#align category_theory.additive_yoneda_obj CategoryTheory.additive_yonedaObj

instance additive_yonedaObj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where
#align category_theory.additive_yoneda_obj' CategoryTheory.additive_yonedaObj'

instance additive_coyonedaObj (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyonedaObj X) where
#align category_theory.additive_coyoneda_obj CategoryTheory.additive_coyonedaObj

instance additive_coyonedaObj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where
#align category_theory.additive_coyoneda_obj' CategoryTheory.additive_coyonedaObj'

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditiveYoneda :
    preadditiveYoneda ⋙
        (whiskeringRight Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat) =
      yoneda :=
  rfl
#align category_theory.whiskering_preadditive_yoneda CategoryTheory.whiskering_preadditiveYoneda

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditiveCoyoneda :
    preadditiveCoyoneda ⋙
        (whiskeringRight C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat) =
      coyoneda :=
  rfl
#align category_theory.whiskering_preadditive_coyoneda CategoryTheory.whiskering_preadditiveCoyoneda

instance full_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat).Full :=
  let _ : Functor.Full (preadditiveYoneda ⋙
      (whiskeringRight Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat)) :=
    Yoneda.yoneda_full
  Functor.Full.of_comp_faithful preadditiveYoneda
    ((whiskeringRight Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat))
#align category_theory.preadditive_yoneda_full CategoryTheory.full_preadditiveYoneda

instance full_preadditiveCoyoneda : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat).Full :=
  let _ : Functor.Full (preadditiveCoyoneda ⋙
      (whiskeringRight C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat)) :=
    Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful preadditiveCoyoneda
    ((whiskeringRight C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat))
#align category_theory.preadditive_coyoneda_full CategoryTheory.full_preadditiveCoyoneda

instance faithful_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveYoneda
#align category_theory.preadditive_yoneda_faithful CategoryTheory.faithful_preadditiveYoneda

instance faithful_preadditiveCoyoneda :
    (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveCoyoneda
#align category_theory.preadditive_coyoneda_faithful CategoryTheory.faithful_preadditiveCoyoneda

end CategoryTheory
