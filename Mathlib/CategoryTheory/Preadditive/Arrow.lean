/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The category of arrows of a preadditive category is preadditive

If `T` is a preadditive category, then there is a structure of preadditive category on `Arrow T`
such that addition commutes with the left and right projections of morphisms of arrows.

## Tags

arrow, preadditive
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {T : Type u} [Category.{v} T] [Preadditive T] {u v : Arrow T}

instance : Add (u ⟶ v) where
  add α β := Arrow.homMk (α.left + β.left) (α.right + β.right) (by simp)

@[simp]
lemma Arrow.Hom.add_left (α β : u ⟶ v) : (α + β).left = α.left + β.left := rfl

@[simp]
lemma Arrow.Hom.add_right (α β : u ⟶ v) : (α + β).right = α.right + β.right := rfl

instance : Zero (u ⟶ v) where
  zero := Arrow.homMk 0 0

@[simp]
lemma Arrow.Hom.zero_left : (0 : u ⟶ v).left = 0 := rfl

@[simp]
lemma Arrow.Hom.zero_right : (0 : u ⟶ v).right = 0 := rfl

instance : Neg (u ⟶ v) where
  neg α := Arrow.homMk (- α.left) (- α.right)

@[simp]
lemma Arrow.Hom.neg_left (α : u ⟶ v) : (- α).left = - α.left := rfl

@[simp]
lemma Arrow.Hom.neg_right (α : u ⟶ v) : (- α).right = - α.right := rfl

instance : AddCommGroup (u ⟶ v) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by cat_disch
  add_zero _ := by cat_disch
  add_comm _ _ := by ext <;> simp [add_comm]
  neg_add_cancel _ := by cat_disch
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- If a category `T` is preadditive, then so is its category of arrows.
-/
instance : Preadditive (Arrow T) where

end CategoryTheory
