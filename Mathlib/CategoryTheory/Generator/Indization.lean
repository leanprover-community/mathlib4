/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Separating set in the category of ind-objects

We construct a separating set in the category of ind-objects.

## Future work

Once we have constructed zero morphisms in the category of ind-objects, we will be able to show
that under sufficient conditions, the category of ind-objects has a separating object.

-/

universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C]

theorem Ind.isSeparating_range_yoneda : IsSeparating (Set.range (Ind.yoneda : C ⥤ _).obj) := by
  refine fun X Y f g h => (cancel_epi (Ind.colimitPresentationCompYoneda X).hom).1 ?_
  exact colimit.hom_ext (fun i => by simp [← Category.assoc, h])

end

end CategoryTheory
