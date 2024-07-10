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

instance : CartesianClosed (LightProfinite.{u}ᵒᵖ ⥤ Type u) := by
  -- We need to consider `LightProfinite` as a small category:
  let e : LightProfinite.{u}ᵒᵖ ⥤ Type u ≌ (SmallModel.{u, u, u+1} LightProfinite.{u})ᵒᵖ ⥤ Type u :=
    Functor.asEquivalence ((whiskeringLeft _ _ _).obj (equivSmallModel _).op.inverse)
  -- Now we conclude because the category of functors from a small category to a cartesian closed
  -- category is cartesian closed.
  exact cartesianClosedOfEquiv e.symm


instance : CartesianClosed (LightCondSet.{u}) :=
  inferInstanceAs (CartesianClosed (Sheaf _ _))
