/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.Condensed.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
/-!

# Condensed sets form a Cartesian closed category
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

instance : CartesianMonoidalCategory (CondensedSet.{u}) :=
  inferInstanceAs (CartesianMonoidalCategory (Sheaf _ _))

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : MonoidalClosed (CondensedSet.{u}) := inferInstanceAs (MonoidalClosed (Sheaf _ _))
