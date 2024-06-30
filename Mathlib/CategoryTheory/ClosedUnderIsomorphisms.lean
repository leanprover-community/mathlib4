/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.Order.Basic

/-! # Predicates on objects which are closed under isomorphisms

This file introduces the type class `ClosedUnderIsomorphisms P` for predicates
`P : C → Prop` on the objects of a category `C`.

-/

namespace CategoryTheory

variable {C : Type*} [Category C] (P Q : C → Prop)

/-- A predicate `C → Prop` on the objects of a category is closed under isomorphisms
if whenever `P X`, then all the objects `Y` that are isomorphic to `X` also satisfy `P Y`. -/
class ClosedUnderIsomorphisms : Prop where
  of_iso {X Y : C} (_ : X ≅ Y) (_ : P X) : P Y

lemma mem_of_iso [ClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y :=
  ClosedUnderIsomorphisms.of_iso e hX

lemma mem_iff_of_iso [ClosedUnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y :=
  ⟨mem_of_iso P e, mem_of_iso P e.symm⟩

lemma mem_of_isIso [ClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : P X) : P Y :=
  mem_of_iso P (asIso f) hX

lemma mem_iff_of_isIso [ClosedUnderIsomorphisms P] {X Y : C} (f : X ⟶ Y) [IsIso f] : P X ↔ P Y :=
  mem_iff_of_iso P (asIso f)

/-- The closure by isomorphisms of a predicate on objects in a category. -/
def isoClosure : C → Prop := fun X => ∃ (Y : C) (_ : P Y), Nonempty (X ≅ Y)

lemma mem_isoClosure_iff (X : C) :
    isoClosure P X ↔ ∃ (Y : C) (_ : P Y), Nonempty (X ≅ Y) := by rfl

variable {P} in
lemma mem_isoClosure {X Y : C} (h : P X) (e : X ⟶ Y) [IsIso e] : isoClosure P Y :=
  ⟨X, h, ⟨(asIso e).symm⟩⟩

lemma le_isoClosure : P ≤ isoClosure P :=
  fun X hX => ⟨X, hX, ⟨Iso.refl X⟩⟩

variable {P Q} in
lemma monotone_isoClosure (h : P ≤ Q) : isoClosure P ≤ isoClosure Q := by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩

lemma isoClosure_eq_self [ClosedUnderIsomorphisms P] : isoClosure P = P := by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact mem_of_iso P e.symm hY
  · exact le_isoClosure P

lemma isoClosure_le_iff [ClosedUnderIsomorphisms Q] : isoClosure P ≤ Q ↔ P ≤ Q :=
  ⟨(le_isoClosure P).trans,
    fun h => (monotone_isoClosure h).trans (by rw [isoClosure_eq_self])⟩

instance : ClosedUnderIsomorphisms (isoClosure P) where
  of_iso := by
    rintro X Y e ⟨Z, hZ, ⟨f⟩⟩
    exact ⟨Z, hZ, ⟨e.symm.trans f⟩⟩

end CategoryTheory
