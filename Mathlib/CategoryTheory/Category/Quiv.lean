/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.category.Quiv
! leanprover-community/mathlib commit 350a381705199e9a070f84e98e803c3c25a97a4c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.PathCategory

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.

-/


universe v u

namespace CategoryTheory

-- intended to be used with explicit universe parameters
/-- Category of quivers. -/
@[nolint check_univs]
def Quiv :=
  Bundled Quiver.{v + 1, u}
#align category_theory.Quiv CategoryTheory.Quiv

namespace Quiv

instance : CoeSort Quiv (Type u) where coe := Bundled.α

instance str (C : Quiv.{v, u}) : Quiver.{v + 1, u} C :=
  C.str
#align category_theory.Quiv.str CategoryTheory.Quiv.str

/-- Construct a bundled `Quiv` from the underlying type and the typeclass. -/
def of (C : Type u) [Quiver.{v + 1} C] : Quiv.{v, u} :=
  Bundled.of C
#align category_theory.Quiv.of CategoryTheory.Quiv.of

instance : Inhabited Quiv :=
  ⟨Quiv.of (Quiver.Empty PEmpty)⟩

/-- Category structure on `Quiv` -/
instance category : LargeCategory.{max v u} Quiv.{v, u}
    where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp C D E F G := Prefunctor.comp F G
  id_comp' C D F := by cases F <;> rfl
  comp_id' C D F := by cases F <;> rfl
  assoc' := by intros <;> rfl
#align category_theory.Quiv.category CategoryTheory.Quiv.category

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ Quiv.{v, u}
    where
  obj C := Quiv.of C
  map C D F := F.toPrefunctor
#align category_theory.Quiv.forget CategoryTheory.Quiv.forget

end Quiv

namespace Cat

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : Quiv.{v, u} ⥤ Cat.{max u v, u}
    where
  obj V := Cat.of (Paths V)
  map V W F :=
    { obj := fun X => F.obj X
      map := fun X Y f => F.mapPath f
      map_comp' := fun X Y Z f g => F.mapPath_comp f g }
  map_id' V := by
    change (show paths V ⥤ _ from _) = _
    ext
    apply eq_conj_eq_to_hom
    rfl
  map_comp' U V W F G := by
    change (show paths U ⥤ _ from _) = _
    ext
    apply eq_conj_eq_to_hom
    rfl
#align category_theory.Cat.free CategoryTheory.Cat.free

end Cat

namespace Quiv

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type _} [Category C] (F : Prefunctor V C) :
    Paths V ⥤ C where
  obj X := F.obj X
  map X Y f := composePath (F.mapPath f)
#align category_theory.Quiv.lift CategoryTheory.Quiv.lift

-- We might construct `of_lift_iso_self : paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ Quiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V C =>
        { toFun := fun F => Paths.of.comp F.toPrefunctor
          invFun := fun F => lift F
          left_inv := fun F => by
            ext
            · erw [(eq_conj_eq_to_hom _).symm]
              apply category.id_comp
            rfl
          right_inv := by
            rintro ⟨obj, map⟩
            dsimp only [Prefunctor.comp]
            congr
            ext (X Y f)
            exact category.id_comp _ }
      homEquiv_naturality_left_symm := fun V W C f g =>
        by
        change (show paths V ⥤ _ from _) = _
        ext
        apply eq_conj_eq_to_hom
        rfl }
#align category_theory.Quiv.adj CategoryTheory.Quiv.adj

end Quiv

end CategoryTheory

