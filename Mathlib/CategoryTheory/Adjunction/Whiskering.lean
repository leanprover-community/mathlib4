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
                           -- ⊢ (𝟭 (C ⥤ D)).map f✝ ≫ (fun X => (Functor.rightUnitor ((𝟭 (C ⥤ D)).obj X)).inv …
                                   -- ⊢ NatTrans.app ((𝟭 (C ⥤ D)).map f✝ ≫ (fun X => (Functor.rightUnitor ((𝟭 (C ⥤ D …
                                        -- ⊢ NatTrans.app f✝ x✝ ≫ 𝟙 (Y✝.obj x✝) ≫ NatTrans.app adj.unit (Y✝.obj x✝) ≫ 𝟙 ( …
                                               -- 🎉 no goals
      counit :=
        { app := fun X =>
            (Functor.associator _ _ _).hom ≫ whiskerLeft X adj.counit ≫ (Functor.rightUnitor _).hom
          naturality := by intros; ext; dsimp; simp }
                           -- ⊢ ((whiskeringRight C E D).obj G ⋙ (whiskeringRight C D E).obj F).map f✝ ≫ (fu …
                                   -- ⊢ NatTrans.app (((whiskeringRight C E D).obj G ⋙ (whiskeringRight C D E).obj F …
                                        -- ⊢ F.map (G.map (NatTrans.app f✝ x✝)) ≫ 𝟙 (F.obj (G.obj (Y✝.obj x✝))) ≫ NatTran …
                                               -- 🎉 no goals
      left_triangle  := by ext; dsimp; simp
                           -- ⊢ NatTrans.app (NatTrans.app (whiskerRight (NatTrans.mk fun X => (Functor.righ …
                                -- ⊢ F.map (𝟙 (x✝¹.obj x✝) ≫ NatTrans.app adj.unit (x✝¹.obj x✝) ≫ 𝟙 (G.obj (F.obj …
                                       -- 🎉 no goals
      right_triangle := by ext; dsimp; simp
                           -- ⊢ NatTrans.app (NatTrans.app (whiskerLeft ((whiskeringRight C E D).obj G) (Nat …
                                -- ⊢ (𝟙 (G.obj (x✝¹.obj x✝)) ≫ NatTrans.app adj.unit (G.obj (x✝¹.obj x✝)) ≫ 𝟙 (G. …
                                       -- 🎉 no goals
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
                           -- ⊢ (𝟭 (D ⥤ C)).map f✝ ≫ (fun X => (Functor.leftUnitor ((𝟭 (D ⥤ C)).obj X)).inv  …
                                   -- ⊢ NatTrans.app ((𝟭 (D ⥤ C)).map f✝ ≫ (fun X => (Functor.leftUnitor ((𝟭 (D ⥤ C) …
                                        -- ⊢ NatTrans.app f✝ x✝ ≫ 𝟙 (Y✝.obj x✝) ≫ Y✝.map (NatTrans.app adj.unit x✝) ≫ 𝟙 ( …
                                               -- 🎉 no goals
      counit :=
        { app := fun X =>
            (Functor.associator _ _ _).inv ≫ whiskerRight adj.counit X ≫ (Functor.leftUnitor _).hom
          naturality := by intros; ext; dsimp; simp }
                           -- ⊢ ((whiskeringLeft D E C).obj F ⋙ (whiskeringLeft E D C).obj G).map f✝ ≫ (fun  …
                                   -- ⊢ NatTrans.app (((whiskeringLeft D E C).obj F ⋙ (whiskeringLeft E D C).obj G). …
                                        -- ⊢ NatTrans.app f✝ (F.obj (G.obj x✝)) ≫ 𝟙 (Y✝.obj (F.obj (G.obj x✝))) ≫ Y✝.map  …
                                               -- 🎉 no goals
      left_triangle  := by ext x; dsimp; simp [Category.id_comp, Category.comp_id, ← x.map_comp]
                           -- ⊢ NatTrans.app (NatTrans.app (whiskerRight (NatTrans.mk fun X => (Functor.left …
                                  -- ⊢ (𝟙 (x.obj (G.obj x✝)) ≫ x.map (NatTrans.app adj.unit (G.obj x✝)) ≫ 𝟙 (x.obj  …
                                         -- 🎉 no goals
      right_triangle := by ext x; dsimp; simp [Category.id_comp, Category.comp_id, ← x.map_comp]
                           -- ⊢ NatTrans.app (NatTrans.app (whiskerLeft ((whiskeringLeft D E C).obj F) (NatT …
                                  -- ⊢ (𝟙 (x.obj (F.obj x✝)) ≫ x.map (F.map (NatTrans.app adj.unit x✝)) ≫ 𝟙 (x.obj  …
                                         -- 🎉 no goals
    }
#align category_theory.adjunction.whisker_left CategoryTheory.Adjunction.whiskerLeft

end CategoryTheory.Adjunction
