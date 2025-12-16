/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# Dual Functors for Rigid Categories

This file defines the left and right dual functors from a rigid monoidal category
to `(Cᵒᵖ)ᴹᵒᵖ` (the monoidal opposite of the opposite category).

## Main definitions

* `leftDualFunctor C`: For a left rigid category, the functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sending
  `X` to `ᘁX` and `f` to `ᘁf`.
* `rightDualFunctor C`: For a right rigid category, the functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sending
  `X` to `Xᘁ` and `f` to `fᘁ`.

## Future work

* Show that in a `RigidCategory`, these functors are monoidal equivalences.
-/

namespace CategoryTheory

open Category MonoidalCategory MonoidalOpposite Opposite

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

section LeftRigid

variable [LeftRigidCategory C]

/-- The left dual functor from `C` to `(Cᵒᵖ)ᴹᵒᵖ`. -/
def leftDualFunctor : C ⥤ (Cᵒᵖ)ᴹᵒᵖ where
  obj X := mop (op (ᘁX))
  map f := (ᘁf).op.mop
  map_id X := by simp [leftAdjointMate_id]
  map_comp f g := by simp [comp_leftAdjointMate]

@[simp]
lemma leftDualFunctor_obj (X : C) : (leftDualFunctor C).obj X = mop (op (ᘁX)) := rfl

@[simp]
lemma leftDualFunctor_map {X Y : C} (f : X ⟶ Y) :
    (leftDualFunctor C).map f = (ᘁf).op.mop := rfl

end LeftRigid

section RightRigid

variable [RightRigidCategory C]

/-- The right dual functor from `C` to `(Cᵒᵖ)ᴹᵒᵖ`. -/
def rightDualFunctor : C ⥤ (Cᵒᵖ)ᴹᵒᵖ where
  obj X := mop (op (Xᘁ))
  map f := (fᘁ).op.mop
  map_id X := by simp [rightAdjointMate_id]
  map_comp f g := by simp [comp_rightAdjointMate]

@[simp]
lemma rightDualFunctor_obj (X : C) : (rightDualFunctor C).obj X = mop (op (Xᘁ)) := rfl

@[simp]
lemma rightDualFunctor_map {X Y : C} (f : X ⟶ Y) :
    (rightDualFunctor C).map f = (fᘁ).op.mop := rfl

end RightRigid

end CategoryTheory
