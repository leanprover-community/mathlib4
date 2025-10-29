/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Light.Basic
import Mathlib.Condensed.Light.Instances
/-!

# Light condensed sets form a Cartesian closed category
-/

universe u

noncomputable section

open CategoryTheory

variable {C : Type u} [SmallCategory C]

instance : CartesianMonoidalCategory (LightCondSet.{u}) :=
  inferInstanceAs (CartesianMonoidalCategory (Sheaf _ _))

instance : CartesianClosed (LightCondSet.{u}) := inferInstanceAs (CartesianClosed (Sheaf _ _))
