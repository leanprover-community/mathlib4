/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.preadditive.yoneda.basic
! leanprover-community/mathlib commit 09f981f72d43749f1fa072deade828d9c1e185bb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Yoneda
import Mathbin.CategoryTheory.Preadditive.Opposite
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.Algebra.Category.Group.Preadditive

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
def preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (End Y)
    where
  obj X := ModuleCat.of _ (X.unop ⟶ Y)
  map X X' f :=
    { toFun := fun g => f.unop ≫ g
      map_add' := fun g g' => comp_add _ _ _ _ _ _
      map_smul' := fun r g => Eq.symm <| Category.assoc _ _ _ }
#align category_theory.preadditive_yoneda_obj CategoryTheory.preadditiveYonedaObj

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditive_yoneda_obj`.
-/
@[simps]
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat.{v}
    where
  obj Y := preadditiveYonedaObj Y ⋙ forget₂ _ _
  map Y Y' f :=
    { app := fun X =>
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun g g' => add_comp _ _ _ _ _ _ }
      naturality' := fun X X' g => AddCommGroupCat.ext _ _ _ _ fun x => Category.assoc _ _ _ }
  map_id' X := by
    ext
    simp
  map_comp' X Y Z f g := by
    ext
    simp
#align category_theory.preadditive_yoneda CategoryTheory.preadditiveYoneda

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveCoyonedaObj (X : Cᵒᵖ) : C ⥤ ModuleCat.{v} (End X)
    where
  obj Y := ModuleCat.of _ (unop X ⟶ Y)
  map Y Y' f :=
    { toFun := fun g => g ≫ f
      map_add' := fun g g' => add_comp _ _ _ _ _ _
      map_smul' := fun r g => Category.assoc _ _ _ }
#align category_theory.preadditive_coyoneda_obj CategoryTheory.preadditiveCoyonedaObj

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditive_coyoneda_obj`.
-/
@[simps]
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat.{v}
    where
  obj X := preadditiveCoyonedaObj X ⋙ forget₂ _ _
  map X X' f :=
    { app := fun Y =>
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun g g' => comp_add _ _ _ _ _ _ }
      naturality' := fun Y Y' g =>
        AddCommGroupCat.ext _ _ _ _ fun x => Eq.symm <| Category.assoc _ _ _ }
  map_id' X := by
    ext
    simp
  map_comp' X Y Z f g := by
    ext
    simp
#align category_theory.preadditive_coyoneda CategoryTheory.preadditiveCoyoneda

instance additive_yoneda_obj (X : C) : Functor.Additive (preadditiveYonedaObj X) where
#align category_theory.additive_yoneda_obj CategoryTheory.additive_yoneda_obj

instance additive_yoneda_obj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where
#align category_theory.additive_yoneda_obj' CategoryTheory.additive_yoneda_obj'

instance additive_coyoneda_obj (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyonedaObj X) where
#align category_theory.additive_coyoneda_obj CategoryTheory.additive_coyoneda_obj

instance additive_coyoneda_obj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where
#align category_theory.additive_coyoneda_obj' CategoryTheory.additive_coyoneda_obj'

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

instance preadditiveYonedaFull : Full (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat) :=
  let yoneda_full :
    Full
      (preadditiveYoneda ⋙
        (whiskeringRight Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat)) :=
    Yoneda.yonedaFull
  full.of_comp_faithful preadditive_yoneda
    ((whiskering_right Cᵒᵖ AddCommGroupCat (Type v)).obj (forget AddCommGroupCat))
#align category_theory.preadditive_yoneda_full CategoryTheory.preadditiveYonedaFull

instance preadditiveCoyonedaFull : Full (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat) :=
  let coyoneda_full :
    Full
      (preadditiveCoyoneda ⋙
        (whiskeringRight C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat)) :=
    Coyoneda.coyonedaFull
  full.of_comp_faithful preadditive_coyoneda
    ((whiskering_right C AddCommGroupCat (Type v)).obj (forget AddCommGroupCat))
#align category_theory.preadditive_coyoneda_full CategoryTheory.preadditiveCoyonedaFull

instance preadditiveYoneda_faithful : Faithful (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroupCat) :=
  Faithful.of_comp_eq whiskering_preadditiveYoneda
#align category_theory.preadditive_yoneda_faithful CategoryTheory.preadditiveYoneda_faithful

instance preadditiveCoyoneda_faithful :
    Faithful (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroupCat) :=
  Faithful.of_comp_eq whiskering_preadditiveCoyoneda
#align category_theory.preadditive_coyoneda_faithful CategoryTheory.preadditiveCoyoneda_faithful

end CategoryTheory

