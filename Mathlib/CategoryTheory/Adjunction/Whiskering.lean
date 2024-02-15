/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Adjunction.Basic

#align_import category_theory.adjunction.whiskering from "leanprover-community/mathlib"@"28aa996fc6fb4317f0083c4e6daf79878d81be33"

/-!

Given categories `C D E`, functors `F : D ⥤ E` and `G : E ⥤ D` with an adjunction
`F ⊣ G`, we provide the induced adjunction between the functor categories `C ⥤ D` and `C ⥤ E`,
and the functor categories `E ⥤ C` and `D ⥤ C`.

-/


namespace CategoryTheory.Adjunction

open CategoryTheory

variable (C : Type*) {D E : Type*} [Category C] [Category D] [Category E] {F : D ⥤ E} {G : E ⥤ D}

/-- Given an adjunction `F ⊣ G`, this provides the natural adjunction
  `(whiskeringRight C _ _).obj F ⊣ (whiskeringRight C _ _).obj G`. -/
@[simps! unit_app_app counit_app_app]
protected def whiskerRight (adj : F ⊣ G) :
    (whiskeringRight C D E).obj F ⊣ (whiskeringRight C E D).obj G :=
  mkOfUnitCounit
    { unit :=
        { app := fun X =>
            (Functor.rightUnitor _).inv ≫ whiskerLeft X adj.unit ≫ (Functor.associator _ _ _).inv
          naturality := by intros; ext; dsimp; simp }
      counit :=
        { app := fun X =>
            (Functor.associator _ _ _).hom ≫ whiskerLeft X adj.counit ≫ (Functor.rightUnitor _).hom
          naturality := by intros; ext; dsimp; simp }
      left_triangle  := by ext; dsimp; simp
      right_triangle := by ext; dsimp; simp
    }
#align category_theory.adjunction.whisker_right CategoryTheory.Adjunction.whiskerRight

/-- Given an adjunction `F ⊣ G`, this provides the natural adjunction
  `(whiskeringLeft _ _ C).obj G ⊣ (whiskeringLeft _ _ C).obj F`. -/
@[simps! unit_app_app counit_app_app]
protected def whiskerLeft (adj : F ⊣ G) :
    (whiskeringLeft E D C).obj G ⊣ (whiskeringLeft D E C).obj F :=
  mkOfUnitCounit
    { unit :=
        { app := fun X =>
            (Functor.leftUnitor _).inv ≫ whiskerRight adj.unit X ≫ (Functor.associator _ _ _).hom
          naturality := by intros; ext; dsimp; simp }
      counit :=
        { app := fun X =>
            (Functor.associator _ _ _).inv ≫ whiskerRight adj.counit X ≫ (Functor.leftUnitor _).hom
          naturality := by intros; ext; dsimp; simp }
      left_triangle  := by ext x; dsimp; simp [Category.id_comp, Category.comp_id, ← x.map_comp]
      right_triangle := by ext x; dsimp; simp [Category.id_comp, Category.comp_id, ← x.map_comp]
    }
#align category_theory.adjunction.whisker_left CategoryTheory.Adjunction.whiskerLeft

end CategoryTheory.Adjunction
