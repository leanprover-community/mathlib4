/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Category.Basic

#align_import category_theory.category.Rel from "leanprover-community/mathlib"@"afad8e438d03f9d89da2914aa06cb4964ba87a18"

/-!
The category of types with binary relations as morphisms.
-/


namespace CategoryTheory

universe u

-- This file is about Lean 3 declaration "Rel".
set_option linter.uppercaseLean3 false

/-- A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def RelCat :=
  Type u
#align category_theory.Rel CategoryTheory.RelCat

instance RelCat.inhabited : Inhabited RelCat := by unfold RelCat; infer_instance
#align category_theory.Rel.inhabited CategoryTheory.RelCat.inhabited

/-- The category of types with binary relations as morphisms. -/
instance rel : LargeCategory RelCat where
  Hom X Y := X → Y → Prop
  id X x y := x = y
  comp f g x z := ∃ y, f x y ∧ g y z
#align category_theory.rel CategoryTheory.rel

end CategoryTheory
