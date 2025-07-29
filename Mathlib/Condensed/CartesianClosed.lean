/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
/-!

# Condensed sets form a cartesian closed category
-/

universe u

noncomputable section

open CategoryTheory

instance : CartesianMonoidalCategory (CondensedSet.{u}) :=
  inferInstanceAs (CartesianMonoidalCategory (Sheaf _ _))

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : CartesianClosed (CondensedSet.{u}) := inferInstanceAs (CartesianClosed (Sheaf _ _))
