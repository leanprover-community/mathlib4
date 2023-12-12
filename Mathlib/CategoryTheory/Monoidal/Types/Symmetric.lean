/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Symmetric
import Mathlib.CategoryTheory.Monoidal.Types.Basic

#align_import category_theory.monoidal.types.symmetric from "leanprover-community/mathlib"@"95a87616d63b3cb49d3fe678d416fbe9c4217bf4"

/-!
# The category of types is a symmetric monoidal category
-/


open CategoryTheory Limits

universe v u

namespace CategoryTheory

open MonoidalCategory

instance typesSymmetric : SymmetricCategory.{u} (Type u) :=
  symmetricOfChosenFiniteProducts Types.terminalLimitCone Types.binaryProductLimitCone
#align category_theory.types_symmetric CategoryTheory.typesSymmetric

@[simp]
theorem braiding_hom_apply {X Y : Type u} {x : X} {y : Y} :
    ((β_ X Y).hom : X ⊗ Y → Y ⊗ X) (x, y) = (y, x) :=
  rfl
#align category_theory.braiding_hom_apply CategoryTheory.braiding_hom_apply

@[simp]
theorem braiding_inv_apply {X Y : Type u} {x : X} {y : Y} :
    ((β_ X Y).inv : Y ⊗ X → X ⊗ Y) (y, x) = (x, y) :=
  rfl
#align category_theory.braiding_inv_apply CategoryTheory.braiding_inv_apply

end CategoryTheory
