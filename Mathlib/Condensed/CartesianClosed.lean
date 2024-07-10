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

instance : CartesianClosed (CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) :=
  -- We need to make `CompHaus` a small category relative to `Type (u+1)`:
  let e : CompHaus.{u}ᵒᵖ ⥤ Type (u+1) ≌ (ULiftHom.{u+1} (CompHaus.{u}))ᵒᵖ ⥤ Type (u+1) :=
    Functor.asEquivalence ((whiskeringLeft _ _ _).obj ULiftHom.equiv.op.inverse)
  -- Now we conclude because the category of functors from a small category to a cartesian closed
  -- category is cartesian closed.
  cartesianClosedOfEquiv e.symm

instance : CartesianClosed (CondensedSet.{u}) :=
  inferInstanceAs (CartesianClosed (Sheaf _ _))
