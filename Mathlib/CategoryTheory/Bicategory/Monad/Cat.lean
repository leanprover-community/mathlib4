import Mathlib.CategoryTheory.Bicategory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Category.Cat


namespace CategoryTheory

open Category Bicategory

universe v₁ u₁

variable (C : Type u₁) [Category.{v₁} C]

example (T : Monad C) : Bicategory.Monad (Cat.of C) where
  t := (T : C ⥤ C)
  μ := T.μ
  η := T.η
  assoc := by
    apply NatTrans.ext
    ext x
    dsimp
    -- simp [Cat.comp_obj, - Strict.associator_eqToIso]
    rw [NatTrans.comp_app, NatTrans.comp_app]
    simp only [Cat.comp_obj, Cat.whiskerRight_app, Cat.whiskerLeft_app]
    -- congr
    rw [T.assoc]
    rw [← NatTrans.comp_app]
    rw [← whiskerLeft_app]
    rw [← NatTrans.comp_app]
    apply NatTrans.congr_app

    rw [← Cat.comp_obj]
    rw [← NatTrans.comp_app]
    simp
  left_unit := _
  right_unit := _
