/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Order.Basic

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

lemma le_def {P Q : ObjectProperty C} :
    P ≤ Q ↔ ∀ (X : C), P X → Q X := Iff.rfl

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

/-- The strict image of a property of objects by a functor. -/
inductive strictMap (P : ObjectProperty C) (F : C ⥤ D) : ObjectProperty D
  | mk (X : C) (hX : P X) : strictMap P F (F.obj X)

lemma strictMap_iff (P : ObjectProperty C) (F : C ⥤ D) (Y : D) :
    P.strictMap F Y ↔ ∃ (X : C), P X ∧ F.obj X = Y :=
  ⟨by rintro ⟨X, hX⟩; exact ⟨X, hX, rfl⟩, by rintro ⟨X, hX, rfl⟩; exact ⟨X, hX⟩⟩

lemma strictMap_obj (P : ObjectProperty C) (F : C ⥤ D) {X : C} (hX : P X) :
    P.strictMap F (F.obj X) :=
  ⟨X, hX⟩

/-- The typeclass associated to `P : ObjectProperty C`. -/
@[mk_iff]
class Is (P : ObjectProperty C) (X : C) : Prop where
  prop : P X

lemma prop_of_is (P : ObjectProperty C) (X : C) [P.Is X] : P X := by rwa [← P.is_iff]

lemma is_of_prop (P : ObjectProperty C) {X : C} (hX : P X) : P.Is X := by rwa [P.is_iff]

section

variable {ι : Type u'} (X : ι → C)

/-- The property of objects that is satisfied by the `X i` for a family
of objects `X : ι : C`. -/
inductive ofObj : ObjectProperty C
  | mk (i : ι) : ofObj (X i)

@[simp]
lemma ofObj_apply (i : ι) : ofObj X (X i) := ⟨i⟩

lemma ofObj_iff (Y : C) : ofObj X Y ↔ ∃ i, X i = Y := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i⟩

lemma ofObj_le_iff (P : ObjectProperty C) :
    ofObj X ≤ P ↔ ∀ i, P (X i) :=
  ⟨fun h i ↦ h _ (by simp), fun h ↦ by rintro _ ⟨i⟩; exact h i⟩

@[simp]
lemma strictMap_ofObj (F : C ⥤ D) :
    (ofObj X).strictMap F = ofObj (F.obj ∘ X) := by
  ext Y
  simp [ofObj_iff, strictMap_iff]

end

/-- The property of objects in a category that is satisfied by a single object `X : C`. -/
abbrev singleton (X : C) : ObjectProperty C := ofObj (fun (_ : Unit) ↦ X)

@[simp]
lemma singleton_iff (X Y : C) : singleton X Y ↔ X = Y := by simp [ofObj_iff]

@[simp]
lemma singleton_le_iff {X : C} {P : ObjectProperty C} :
    singleton X ≤ P ↔ P X := by
  simp [ofObj_le_iff]

@[simp high]
lemma strictMap_singleton (X : C) (F : C ⥤ D) :
    (singleton X).strictMap F = singleton (F.obj X) := by
  ext
  simp [strictMap_iff]

/-- The property of objects in a category that is satisfied by `X : C` and `Y : C`. -/
def pair (X Y : C) : ObjectProperty C :=
  ofObj (Sum.elim (fun (_ : Unit) ↦ X) (fun (_ : Unit) ↦ Y))

@[simp]
lemma pair_iff (X Y Z : C) :
    pair X Y Z ↔ X = Z ∨ Y = Z := by
  constructor
  · rintro ⟨_ | _⟩ <;> tauto
  · rintro (rfl | rfl); exacts [⟨Sum.inl .unit⟩, ⟨Sum.inr .unit⟩]

end ObjectProperty

end CategoryTheory
