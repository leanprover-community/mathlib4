/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal

/-!
# A closed monoidal category is enriched in itself

From the data of a closed monoidal category C, we define a C-category structure for C
where the hom-object is given by the internal hom (coming from the closed structure).

The instance is given at the end of the file.

We use `scoped instance` to avoid potential issues where C may also have
a C-category structure coming from another source (e.g. the type of simplicial sets
`SSet.{v}` has an instance of `EnrichedCategory SSet.{v}` as a category of simplicial objects;
see `AlgebraicTopology/SimplicialCategory/SimplicialObject`).

All structure field values are defined in `Closed/Monoidal`

-/

universe u v

namespace CategoryTheory

namespace MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- For C closed monoidal, build an instance of C as a C-category -/
scoped instance : EnrichedCategory C C where
  Hom x := (ihom x).obj
  id x := @id C _ _ x _
  comp x y z := @comp C _ _ x y z _ _
  id_comp x y := @id_comp C _ _ x y _
  comp_id x y := @comp_id C _ _ x y _ _
  assoc x y z w := @assoc C _ _ x y z w _ _ _

end MonoidalClosed

end CategoryTheory
