/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.types.symmetric
! leanprover-community/mathlib commit 95a87616d63b3cb49d3fe678d416fbe9c4217bf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.OfChosenFiniteProducts.Symmetric
import Mathbin.CategoryTheory.Monoidal.Types.Basic

/-!
# The category of types is a symmetric monoidal category
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

instance typesSymmetric : SymmetricCategory.{u} (Type u) :=
  symmetricOfChosenFiniteProducts Types.terminalLimitCone Types.binaryProductLimitCone
#align category_theory.types_symmetric CategoryTheory.typesSymmetric

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem braiding_hom_apply {X Y : Type u} {x : X} {y : Y} :
    ((β_ X Y).Hom : X ⊗ Y → Y ⊗ X) (x, y) = (y, x) :=
  rfl
#align category_theory.braiding_hom_apply CategoryTheory.braiding_hom_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem braiding_inv_apply {X Y : Type u} {x : X} {y : Y} :
    ((β_ X Y).inv : Y ⊗ X → X ⊗ Y) (y, x) = (x, y) :=
  rfl
#align category_theory.braiding_inv_apply CategoryTheory.braiding_inv_apply

end CategoryTheory

