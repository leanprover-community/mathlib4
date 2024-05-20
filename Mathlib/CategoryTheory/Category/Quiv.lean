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

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.

-/


universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of quivers. -/
@[nolint checkUnivs]
def Quiv :=
  Bundled Quiver.{v + 1, u}
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv CategoryTheory.Quiv

namespace Quiv

instance : CoeSort Quiv (Type u) where coe := Bundled.α

instance str' (C : Quiv.{v, u}) : Quiver.{v + 1, u} C :=
  C.str
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.str CategoryTheory.Quiv.str'

/-- Construct a bundled `Quiv` from the underlying type and the typeclass. -/
def of (C : Type u) [Quiver.{v + 1} C] : Quiv.{v, u} :=
  Bundled.of C
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.of CategoryTheory.Quiv.of

instance : Inhabited Quiv :=
  ⟨Quiv.of (Quiver.Empty PEmpty)⟩

/-- Category structure on `Quiv` -/
instance category : LargeCategory.{max v u} Quiv.{v, u} where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.category CategoryTheory.Quiv.category

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ Quiv.{v, u} where
  obj C := Quiv.of C
  map F := F.toPrefunctor
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.forget CategoryTheory.Quiv.forget

end Quiv

namespace Cat

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Paths V)
  map F :=
    { obj := fun X => F.obj X
      map := fun f => F.mapPath f
      map_comp := fun f g => F.mapPath_comp f g }
  map_id V := by
    change (show Paths V ⥤ _ from _) = _
    ext; swap
    · apply eq_conj_eqToHom
    · rfl
  map_comp {U _ _} F G := by
    change (show Paths U ⥤ _ from _) = _
    ext; swap
    · apply eq_conj_eqToHom
    · rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.free CategoryTheory.Cat.free

end Cat

namespace Quiv

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type*} [Category C] (F : Prefunctor V C) :
    Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.lift CategoryTheory.Quiv.lift

-- We might construct `of_lift_iso_self : Paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ Quiv.forget :=
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
        · apply eq_conj_eqToHom
        · rfl }
set_option linter.uppercaseLean3 false in
#align category_theory.Quiv.adj CategoryTheory.Quiv.adj

end Quiv

end CategoryTheory
