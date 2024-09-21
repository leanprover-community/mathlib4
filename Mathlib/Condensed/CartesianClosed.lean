/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Limits
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.CartesianClosed
/-!

# Condensed sets form a cartesian closed category
-/

universe u

noncomputable section

open CategoryTheory

instance : CartesianClosed (CondensedSet.{u}) := inferInstanceAs (CartesianClosed (Sheaf _ _))
