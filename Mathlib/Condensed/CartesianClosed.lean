/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Closed.Types
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.Condensed.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact

@[expose] public section
/-!

# Condensed sets form a Cartesian-closed category
-/

universe u

noncomputable section

open CategoryTheory

instance : CartesianMonoidalCategory (CondensedSet.{u}) :=
  inferInstanceAs (CartesianMonoidalCategory (Sheaf _ _))

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : CartesianClosed (CondensedSet.{u}) := inferInstanceAs (CartesianClosed (Sheaf _ _))
