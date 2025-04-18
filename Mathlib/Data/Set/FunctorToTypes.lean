/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types
import Mathlib.Data.Set.Basic

/-!
# The functor from `Set X` to types

Given `X : Type u`, we define the functor `Set.functorToTypes : Set X ⥤ Type u`
which sends `A : Set X` to its underlying type.

-/

universe u

open CategoryTheory

namespace Set

/-- Given `X : Type u`, this the functor `Set X ⥤ Type u` which sends `A`
to its underlying type. -/
@[simps obj map]
def functorToTypes {X : Type u} : Set X ⥤ Type u where
  obj S := S
  map {S T} f := fun ⟨x, hx⟩ ↦ ⟨x, leOfHom f hx⟩

end Set
