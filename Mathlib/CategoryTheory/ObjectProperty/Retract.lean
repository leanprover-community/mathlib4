/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Retract

/-! # Properties of objects which are stable under retracts

Given a category `C` and `P : ObjectProperty C` (i.e. `P : C → Prop`),
this file introduces the type class `P.IsStableUnderRetracts`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- A predicate `C → Prop` on the objects of a category is stable under retracts
if whenever `P Y`, then all the objects `X` that are retracts of `Y` also satisfy `P X`. -/
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

lemma retractClosure_isoClosure :
    P.isoClosure.retractClosure = P.retractClosure := by
  refine le_antisymm ?_ (monotone_retractClosure P.le_isoClosure)
  rintro Y ⟨X, ⟨X', hX', ⟨e⟩⟩, ⟨h⟩⟩
  exact ⟨_, hX', ⟨h.trans (Retract.ofIso e)⟩⟩

instance : IsStableUnderRetracts (retractClosure P) where
  of_retract := by
    rintro X Y r₁ ⟨Z, hZ, ⟨r₂⟩⟩
    refine ⟨Z, hZ, ⟨r₁.trans r₂⟩⟩

instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} P.retractClosure where
  exists_small_le' := by
    obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} P
    let α := Σ (X : Subtype Q), { p : X.1 ⟶ X.1 // p ≫ p = p }
    let g {X Y : C} (h : Retract Y X) (hX : Q X) : α := ⟨⟨X, hX⟩, h.r ≫ h.i, by simp⟩
    let R (a : α) : Prop := ∃ (X Y : C) (h : Retract Y X) (hX : Q X), g h hX = a
    choose X Y h hX using fun (a : Subtype R) ↦ a.2
    refine ⟨.ofObj Y, inferInstance, (monotone_retractClosure h₂).trans ?_⟩
    rw [retractClosure_isoClosure]
    rintro y ⟨x, hx, ⟨r⟩⟩
    obtain ⟨a, h₁, h₂⟩ : ∃ (a : Subtype R) (h₁ : Q (X a)), g (h a) h₁ = g r hx := by
      obtain ⟨_, hr⟩ := hX ⟨⟨⟨_, hx⟩, r.r ≫ r.i, by simp⟩, ⟨_, _, r, hx, rfl⟩⟩
      exact ⟨_, _, hr⟩
    obtain rfl : x = X a := Subtype.ext_iff.1 (congr_arg Sigma.fst h₂.symm)
    have hri : (h a).r ≫ (h a).i = r.r ≫ r.i := by
      rw [Sigma.ext_iff, heq_eq_eq] at h₂
      exact Subtype.ext_iff.1 h₂.2
    exact ⟨_, ⟨a.1, a.2⟩, ⟨{
      hom := r.i ≫ (h a).r
      inv := (h a).i ≫ r.r
      hom_inv_id := by simp [reassoc_of% hri]
      inv_hom_id := by simp [← reassoc_of% hri]
    }⟩⟩

end CategoryTheory.ObjectProperty
