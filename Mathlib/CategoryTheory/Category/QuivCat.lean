/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.PathCategory

#align_import category_theory.category.Quiv from "leanprover-community/mathlib"@"350a381705199e9a070f84e98e803c3c25a97a4c"

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `QuivCat`.

-/


universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of quivers. -/
@[nolint checkUnivs]
def QuivCat :=
  Bundled Quiver.{v + 1, u}
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv CategoryTheory.QuivCat

namespace QuivCat

instance : CoeSort QuivCat (Type u) where coe := Bundled.α

instance str' (C : QuivCat.{v, u}) : Quiver.{v + 1, u} C :=
  C.str
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.str CategoryTheory.QuivCat.str'

/-- Construct a bundled `QuivCat` from the underlying type and the typeclass. -/
def of (C : Type u) [Quiver.{v + 1} C] : QuivCat.{v, u} :=
  Bundled.of C
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.of CategoryTheory.QuivCat.of

instance : Inhabited QuivCat :=
  ⟨QuivCat.of (Quiver.Empty PEmpty)⟩

/-- Category structure on `QuivCat` -/
instance category : LargeCategory.{max v u} QuivCat.{v, u}
    where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.category CategoryTheory.QuivCat.category

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ QuivCat.{v, u}
    where
  obj C := QuivCat.of C
  map F := F.toPrefunctor
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.forget CategoryTheory.QuivCat.forget

end QuivCat

namespace Cat

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : QuivCat.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Paths V)
  map F :=
    { obj := fun X => F.obj X
      map := fun f => F.mapPath f
      map_comp := fun f g => F.mapPath_comp f g }
  map_id V := by
    change (show Paths V ⥤ _ from _) = _
    ext; swap
    apply eq_conj_eqToHom
    rfl
  map_comp {U _ _} F G := by
    change (show Paths U ⥤ _ from _) = _
    ext; swap
    apply eq_conj_eqToHom
    rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.free CategoryTheory.Cat.free

end Cat

namespace QuivCat

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type*} [Category C] (F : Prefunctor V C) :
    Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.lift CategoryTheory.QuivCat.lift

-- We might construct `of_lift_iso_self : Paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ QuivCat.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V C =>
        { toFun := fun F => Paths.of.comp F.toPrefunctor
          invFun := fun F => @lift V _ C _ F
          left_inv := fun F => Paths.ext_functor rfl (by simp)
          right_inv := by
            rintro ⟨obj, map⟩
            dsimp only [Prefunctor.comp]
            congr
            funext X Y f
            exact Category.id_comp _ }
      homEquiv_naturality_left_symm := fun {V _ _} f g => by
        change (show Paths V ⥤ _ from _) = _
        ext; swap
        apply eq_conj_eqToHom
        rfl }
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.adj CategoryTheory.QuivCat.adj

end QuivCat

end CategoryTheory
