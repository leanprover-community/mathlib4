/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.Limits
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.CartesianClosed
/-!

# Light condensed sets form a cartesian closed category
-/

universe u

noncomputable section

open CategoryTheory

variable {C : Type u} [SmallCategory C]

instance : CartesianClosed (LightCondSet.{u}) := inferInstanceAs (CartesianClosed (Sheaf _ _))
