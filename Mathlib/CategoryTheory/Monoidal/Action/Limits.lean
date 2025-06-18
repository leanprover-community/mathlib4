/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Left actions of `Type u` on cocomplete categories

If `C` is a category with all coproducts, then `C` admits
a left action from the monoidal category of types.

-/

universe v u

namespace CategoryTheory.MonoidalCategory

variable (C : Type u) [Category.{v} C]
open Limits

-- set_option pp.universes true in
def typeAction.{w} [HasCoproducts.{w} C] : MonoidalLeftAction (Type w) C where
  actionObj J c := (sigmaConst.obj c).obj J
  actionHomLeft f c := (sigmaConst.obj c).map f
  actionHomRight J f := (sigmaConst.obj c).map f


end CategoryTheory.MonoidalCategory
