/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Retract

/-! # Properties of objects which are stable under retracts

Given a category `C` and `P : ObjectProperty C` (i.e. `P : C → Prop`),
this file introduces the type class `P.IsStableUnderRetracts`.
-/

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] (P : ObjectProperty C)

/-- A predicate `C → Prop` on the objects of a category is stable under retracts
if whenever `P Y`, then all the objects `X` that are retracts of `X` also satisfy `P X`. -/
class IsStableUnderRetracts where
  of_retract {X Y : C} (_ : Retract X Y) (_ : P Y) : P X

lemma prop_of_retract [IsStableUnderRetracts P] {X Y : C} (h : Retract X Y) (hY : P Y) : P X :=
  IsStableUnderRetracts.of_retract h hY

/-- The closure by retracts of a predicate on objects in a category. -/
def retractClosure : ObjectProperty C := fun X => ∃ (Y : C) (_ : P Y), Nonempty (Retract X Y)

lemma prop_retractClosure_iff (X : C) :
    retractClosure P X ↔ ∃ (Y : C) (_ : P Y), Nonempty (Retract X Y) := by rfl

variable {P} in
lemma prop_retractClosure {X Y : C} (h : P Y) (r : Retract X Y) : retractClosure P X :=
  ⟨Y, h, ⟨r⟩⟩

lemma le_retractClosure : P ≤ retractClosure P :=
  fun X hX => ⟨X, hX, ⟨Retract.refl X⟩⟩

variable {P Q} in
lemma monotone_retractClosure (h : P ≤ Q) : retractClosure P ≤ retractClosure Q := by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h _ hX', ⟨e⟩⟩

lemma retractClosure_eq_self [IsStableUnderRetracts P] : retractClosure P = P := by
  apply le_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact prop_of_retract P e hY
  · exact le_retractClosure P

lemma retractClosure_le_iff (Q : ObjectProperty C) [IsStableUnderRetracts Q] :
    retractClosure P ≤ Q ↔ P ≤ Q :=
  ⟨(le_retractClosure P).trans,
    fun h => (monotone_retractClosure h).trans (by rw [retractClosure_eq_self])⟩

instance : IsStableUnderRetracts (retractClosure P) where
  of_retract := by
    rintro X Y r₁ ⟨Z, hZ, ⟨r₂⟩⟩
    refine ⟨Z, hZ, ⟨r₁.trans r₂⟩⟩

end CategoryTheory.ObjectProperty
