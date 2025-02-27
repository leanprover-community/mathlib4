/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Basic

/-!
# Properties of objects in a category

Given a category `C`, we introduce an abbreviation `ObjectProperty C`
for predicates `C → Prop`.

## TODO

* refactor the file `Limits.FullSubcategory` in order to rename `ClosedUnderLimitsOfShape`
as `ObjectProperty.IsClosedUnderLimitsOfShape` (and make it a type class)
* refactor the file `Triangulated.Subcategory` in order to make it a type class
regarding terms in `ObjectProperty C` when `C` is pretriangulated

-/

universe v u

namespace CategoryTheory

/-- A property of objects in a category `C` is a predicate `C → Prop`. -/
@[nolint unusedArguments]
abbrev ObjectProperty (C : Type u) [Category.{v} C] : Type u := C → Prop

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- The typeclass associated to `P : ObjectProperty C`. -/
@[mk_iff]
class Is (X : C) : Prop where
  prop : P X

lemma prop_of_is (X : C) [P.Is X] : P X := by rwa [← P.is_iff]

lemma is_of_prop {X : C} (hX : P X) : P.Is X := by rwa [P.is_iff]

end ObjectProperty

end CategoryTheory
