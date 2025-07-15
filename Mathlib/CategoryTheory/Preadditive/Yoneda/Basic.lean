/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.Grp.Yoneda

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


universe v u u₁

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits CategoryTheory.Functor

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
      map_add' := fun _ _ => comp_add _ _ _ _ _ _
      map_smul' := fun _ _ => Eq.symm <| Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditiveYonedaObj`.
-/
@[simps obj]
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrp.{v} where
  obj Y := preadditiveYonedaObj Y ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrp.ofHom
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun _ _ => add_comp _ _ _ _ _ _ }
      naturality := fun _ _ _ => AddCommGrp.ext fun _ => Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditiveCoyonedaObj (X : C) : C ⥤ ModuleCat.{v} (End X)ᵐᵒᵖ where
  obj Y := ModuleCat.of _ (X ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => g ≫ f
      map_add' := fun _ _ => add_comp _ _ _ _ _ _
      map_smul' := fun _ _ => Category.assoc _ _ _ }

/-- The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditiveCoyonedaObj`.
-/
@[simps obj]
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrp.{v} where
  obj X := preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _
  map f :=
    { app := fun _ => AddCommGrp.ofHom
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun _ _ => comp_add _ _ _ _ _ _ }
      naturality := fun _ _ _ =>
        AddCommGrp.ext fun _ => Eq.symm <| Category.assoc _ _ _ }

instance additive_yonedaObj (X : C) : Functor.Additive (preadditiveYonedaObj X) where

instance additive_yonedaObj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where

instance additive_coyonedaObj (X : C) : Functor.Additive (preadditiveCoyonedaObj X) where

instance additive_coyonedaObj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditiveYoneda :
    preadditiveYoneda ⋙
        (whiskeringRight Cᵒᵖ AddCommGrp (Type v)).obj (forget AddCommGrp) =
      yoneda :=
  rfl

/-- Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp]
theorem whiskering_preadditiveCoyoneda :
    preadditiveCoyoneda ⋙
        (whiskeringRight C AddCommGrp (Type v)).obj (forget AddCommGrp) =
      coyoneda :=
  rfl

instance full_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrp).Full :=
  let _ : Functor.Full (preadditiveYoneda ⋙
      (whiskeringRight Cᵒᵖ AddCommGrp (Type v)).obj (forget AddCommGrp)) :=
    Yoneda.yoneda_full
  Functor.Full.of_comp_faithful preadditiveYoneda
    ((whiskeringRight Cᵒᵖ AddCommGrp (Type v)).obj (forget AddCommGrp))

instance full_preadditiveCoyoneda : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrp).Full :=
  let _ : Functor.Full (preadditiveCoyoneda ⋙
      (whiskeringRight C AddCommGrp (Type v)).obj (forget AddCommGrp)) :=
    Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful preadditiveCoyoneda
    ((whiskeringRight C AddCommGrp (Type v)).obj (forget AddCommGrp))

instance faithful_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrp).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveYoneda

instance faithful_preadditiveCoyoneda :
    (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrp).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveCoyoneda

section

variable {D : Type u₁} [Category.{v} D] [Preadditive D] (F : C ⥤ D) [F.Additive]

/-- The natural transformation `preadditiveYoneda.obj X ⟶ F.op ⋙ preadditiveYoneda.obj (F.obj X)`
when `F : C ⥤ D` is an additive functor between preadditive categories and `X : C`. -/
@[simps]
def preadditiveYonedaMap (X : C) :
    preadditiveYoneda.obj X ⟶ F.op ⋙ preadditiveYoneda.obj (F.obj X) where
  app Y := AddCommGrp.ofHom F.mapAddHom

end

/-- The preadditive coyoneda functor for the category `AddCommGrp` agrees with
`AddCommGrp.coyoneda`. -/
def _root_.AddCommGrp.preadditiveCoyonedaIso : preadditiveCoyoneda ≅ AddCommGrp.coyoneda :=
  NatIso.ofComponents fun X ↦ NatIso.ofComponents fun Y ↦ AddCommGrp.homAddEquiv.toAddCommGrpIso

end CategoryTheory
