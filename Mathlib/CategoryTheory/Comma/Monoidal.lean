/-
Copyright (c) 2025 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal structure on the arrow category

-/

universe v u

namespace CategoryTheory.Arrow

open Opposite Limits MonoidalCategory Functor PushoutProduct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (F : C ⥤ C ⥤ C) (G : Cᵒᵖ ⥤ C ⥤ C)

noncomputable
instance [HasPushouts C] [HasInitial C] : MonoidalCategory (Arrow C) where
  tensorObj := ((leftBifunctor F).obj X).obj Y
  whiskerLeft := _
  whiskerRight := _
  tensorUnit := _
  associator := _
  leftUnitor := _
  rightUnitor := _
  tensorHom_def := _
  id_tensorHom_id := _
  tensorHom_comp_tensorHom := _
  whiskerLeft_id := _
  id_whiskerRight := _
  associator_naturality := _
  leftUnitor_naturality := _
  rightUnitor_naturality := _
  pentagon := _
  triangle := _

/-
  tensorObj X Y := ((leftBifunctor F).obj X).obj Y
  whiskerLeft X _ _ f := ((leftBifunctor F).obj X).map f
  whiskerRight f X := ((leftBifunctor F).map f).app X
  tensorUnit := Arrow.mk (initial.to (𝟙_ C))
  associator X Y Z := by

    sorry
  leftUnitor X := sorry
  rightUnitor X := sorry
-/

end CategoryTheory.Arrow
