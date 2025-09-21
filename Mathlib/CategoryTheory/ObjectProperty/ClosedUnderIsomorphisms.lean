/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.Order.Basic

/-! # Properties of objects which are closed under isomorphisms

Given a category `C` and `P : ObjectProperty C` (i.e. `P : C → Prop`),
this file introduces the type class `P.IsClosedUnderIsomorphisms`.

-/

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (P Q : ObjectProperty C)

namespace ObjectProperty

/-- A predicate `C → Prop` on the objects of a category is closed under isomorphisms
if whenever `P X`, then all the objects `Y` that are isomorphic to `X` also satisfy `P Y`. -/
class IsClosedUnderIsomorphisms : Prop where
  of_iso {X Y : C} (_ : X ≅ Y) (_ : P X) : P Y

lemma prop_of_iso [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y :=
  IsClosedUnderIsomorphisms.of_iso e hX

lemma prop_iff_of_iso [IsClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y :=
  ⟨prop_of_iso P e, prop_of_iso P e.symm⟩

lemma prop_of_isIso [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : P X) :
    P Y :=
  prop_of_iso P (asIso f) hX

lemma prop_iff_of_isIso [IsClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] : P X ↔ P Y :=
  prop_iff_of_iso P (asIso f)

/-- The closure by isomorphisms of a predicate on objects in a category. -/
def isoClosure : ObjectProperty C := fun X => ∃ (Y : C) (_ : P Y), Nonempty (X ≅ Y)

lemma prop_isoClosure_iff (X : C) :
    isoClosure P X ↔ ∃ (Y : C) (_ : P Y), Nonempty (X ≅ Y) := by rfl

variable {P} in
lemma prop_isoClosure {X Y : C} (h : P X) (e : X ⟶ Y) [IsIso e] : isoClosure P Y :=
  ⟨X, h, ⟨(asIso e).symm⟩⟩

lemma le_isoClosure : P ≤ isoClosure P :=
  fun X hX => ⟨X, hX, ⟨Iso.refl X⟩⟩

variable {P Q} in
lemma monotone_isoClosure (h : P ≤ Q) : isoClosure P ≤ isoClosure Q := by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩

lemma isoClosure_eq_self [IsClosedUnderIsomorphisms P] : isoClosure P = P := by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_iso P e.symm hY
  · exact le_isoClosure P

lemma isoClosure_le_iff [IsClosedUnderIsomorphisms Q] : isoClosure P ≤ Q ↔ P ≤ Q :=
  ⟨(le_isoClosure P).trans,
    fun h => (monotone_isoClosure h).trans (by rw [isoClosure_eq_self])⟩

instance : IsClosedUnderIsomorphisms (isoClosure P) where
  of_iso := by
    rintro X Y e ⟨Z, hZ, ⟨f⟩⟩
    exact ⟨Z, hZ, ⟨e.symm.trans f⟩⟩

lemma isClosedUnderIsomorphisms_iff_isoClosure_eq_self :
    IsClosedUnderIsomorphisms P ↔ isoClosure P = P :=
  ⟨fun _ ↦ isoClosure_eq_self _, fun h ↦ by rw [← h]; infer_instance⟩

instance (F : C ⥤ D) : IsClosedUnderIsomorphisms (P.map F) where
  of_iso := by
    rintro _ _ e ⟨X, hX, ⟨e'⟩⟩
    exact ⟨X, hX, ⟨e' ≪≫ e⟩⟩

instance (F : D ⥤ C) [P.IsClosedUnderIsomorphisms] :
    IsClosedUnderIsomorphisms (P.inverseImage F) where
  of_iso e hX := P.prop_of_iso (F.mapIso e) hX

end ObjectProperty

end CategoryTheory
