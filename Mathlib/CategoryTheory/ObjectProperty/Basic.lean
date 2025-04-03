/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso

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

universe v v' u u'

namespace CategoryTheory

/-- A property of objects in a category `C` is a predicate `C → Prop`. -/
@[nolint unusedArguments]
abbrev ObjectProperty (C : Type u) [Category.{v} C] : Type u := C → Prop

namespace ObjectProperty

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

/-- The inverse image of a property of objects by a functor. -/
def inverseImage (P : ObjectProperty D) (F : C ⥤ D) : ObjectProperty C :=
  fun X ↦ P (F.obj X)

@[simp]
lemma prop_inverseImage_iff (P : ObjectProperty D) (F : C ⥤ D) (X : C) :
    P.inverseImage F X ↔ P (F.obj X) := Iff.rfl

/-- The essential image of a property of objects by a functor. -/
def map (P : ObjectProperty C) (F : C ⥤ D) : ObjectProperty D :=
  fun Y ↦ ∃ (X : C), P X ∧ Nonempty (F.obj X ≅ Y)

lemma prop_map_iff (P : ObjectProperty C) (F : C ⥤ D) (Y : D) :
    P.map F Y ↔ ∃ (X : C), P X ∧ Nonempty (F.obj X ≅ Y) := Iff.rfl

lemma prop_map_obj (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X) :
    P.map F (F.obj X) :=
  ⟨X, hX, ⟨Iso.refl _⟩⟩

end ObjectProperty

end CategoryTheory
