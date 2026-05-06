/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# The opposite of a triangulated subcategory

In this file, we show that if `P : ObjectProperty C` is a triangulated
subcategory of a pretriangulated category `C`, then `P.op` is a
triangulated subcategory of `Cᵒᵖ`.

-/

public section

namespace CategoryTheory

open Pretriangulated.Opposite Pretriangulated Limits

namespace ObjectProperty

variable {C : Type*} [Category* C]
  [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

instance (P : ObjectProperty C) [P.IsStableUnderShift ℤ] :
    P.op.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := { le_shift _ hX := P.le_shift (-n) _ hX }

instance (P : ObjectProperty Cᵒᵖ) [P.IsStableUnderShift ℤ] :
    P.unop.IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift X hX := by
        obtain ⟨m, rfl⟩ : ∃ m, n = -m := ⟨-n , by simp⟩
        exact P.le_shift m _ hX }

instance (P : ObjectProperty C) [P.IsTriangulatedClosed₂] : P.op.IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := by
    rw [mem_distTriang_op_iff] at hT
    obtain ⟨X, hX, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ hT h₃ h₁
    exact ⟨Opposite.op X, hX, ⟨e.symm.op⟩⟩

instance (P : ObjectProperty Cᵒᵖ) [P.IsTriangulatedClosed₂] : P.unop.IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := by
    obtain ⟨X, hX, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ (op_distinguished _ hT) h₃ h₁
    exact ⟨Opposite.unop X, hX, ⟨e.symm.unop⟩⟩

instance (P : ObjectProperty C) [P.IsTriangulated] : P.op.IsTriangulated where

instance (P : ObjectProperty Cᵒᵖ) [P.IsTriangulated] : P.unop.IsTriangulated where

lemma trW_of_op (P : ObjectProperty C) [P.IsTriangulated]
    {X Y : C} {f : X ⟶ Y} (hf : P.op.trW f.op) : P.trW f := by
  obtain ⟨Z, a, b, h₁, h₂⟩ := hf
  rw [ObjectProperty.trW_iff']
  exact ⟨_, _, _, Pretriangulated.unop_distinguished _ h₁, h₂⟩

lemma trW_of_unop (P : ObjectProperty Cᵒᵖ) [P.IsTriangulated]
    {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : P.unop.trW f.unop) : P.trW f := by
  obtain ⟨Z, a, b, h₁, h₂⟩ := hf
  rw [ObjectProperty.trW_iff']
  exact ⟨_, _, _, Pretriangulated.op_distinguished _ h₁, h₂⟩

lemma trW_op_iff (P : ObjectProperty C) [P.IsTriangulated] {X Y : Cᵒᵖ} {f : X ⟶ Y} :
    P.op.trW f ↔ P.trW f.unop :=
  ⟨P.trW_of_op, P.op.trW_of_unop⟩

lemma trW_op (P : ObjectProperty C) [P.IsTriangulated] : P.op.trW = P.trW.op := by
  ext X Y f
  exact P.trW_op_iff

end ObjectProperty

end CategoryTheory
