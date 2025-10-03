/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Opposites

/-!
# The opposite of a property of objects

-/

universe v u

namespace CategoryTheory.ObjectProperty

open Opposite

variable {C : Type u} [Category.{v} C]

/-- The property of objects of `Cᵒᵖ` corresponding to `P : ObjectProperty C`. -/
protected def op (P : ObjectProperty C) : ObjectProperty Cᵒᵖ :=
  fun X ↦ P X.unop

/-- The property of objects of `C` corresponding to `P : ObjectProperty Cᵒᵖ`. -/
protected def unop (P : ObjectProperty Cᵒᵖ) : ObjectProperty C :=
  fun X ↦ P (op X)

@[simp]
lemma op_iff (P : ObjectProperty C) (X : Cᵒᵖ) :
    P.op X ↔ P X.unop := Iff.rfl

@[simp]
lemma unop_iff (P : ObjectProperty Cᵒᵖ) (X : C) :
    P.unop X ↔ P (op X) := Iff.rfl

@[simp]
lemma op_unop (P : ObjectProperty Cᵒᵖ) : P.unop.op = P := rfl

@[simp]
lemma unop_op (P : ObjectProperty C) : P.op.unop = P := rfl

lemma op_injective {P Q : ObjectProperty C} (h : P.op = Q.op) : P = Q := by
  rw [← P.unop_op, ← Q.unop_op, h]

lemma unop_injective {P Q : ObjectProperty Cᵒᵖ} (h : P.unop = Q.unop) : P = Q := by
  rw [← P.op_unop, ← Q.op_unop, h]

lemma op_injective_iff {P Q : ObjectProperty C} :
    P.op = Q.op ↔ P = Q :=
  ⟨op_injective, by rintro rfl; rfl⟩

lemma unop_injective_iff {P Q : ObjectProperty Cᵒᵖ} :
    P.unop = Q.unop ↔ P = Q :=
  ⟨unop_injective, by rintro rfl; rfl⟩

instance (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    P.op.IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso e.symm.unop hX

instance (P : ObjectProperty Cᵒᵖ) [P.IsClosedUnderIsomorphisms] :
    P.unop.IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso e.symm.op hX

lemma isoClosure_op (P : ObjectProperty C) :
    P.isoClosure.op = P.op.isoClosure := by
  ext ⟨X⟩
  exact ⟨fun ⟨Y, h, ⟨e⟩⟩ ↦ ⟨op Y, h, ⟨e.op.symm⟩⟩,
    fun ⟨Y, h, ⟨e⟩⟩ ↦ ⟨Y.unop, h, ⟨e.unop.symm⟩⟩⟩

lemma isoClosure_unop (P : ObjectProperty Cᵒᵖ) :
    P.isoClosure.unop = P.unop.isoClosure := by
  rw [← op_injective_iff, P.unop.isoClosure_op, op_unop, op_unop]

end CategoryTheory.ObjectProperty
