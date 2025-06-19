/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Opposite
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# The opposite of a triangulated subcategory

-/

namespace CategoryTheory

open Opposite Pretriangulated.Opposite Pretriangulated Triangulated Limits

namespace ObjectProperty

variable {C : Type*} [Category C]
variable [HasShift C ℤ] [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

instance (P : ObjectProperty C) [P.IsTriangulated] : P.op.IsTriangulated where
  isStableUnderShiftBy n :=
    { le_shift X hX := P.le_shift (-n) _ hX }
  ext₂' := by
    rintro T hT h₁ h₃
    rw [mem_distTriang_op_iff] at hT
    obtain ⟨X, hX, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ hT h₃ h₁
    exact ⟨Opposite.op X, hX, ⟨e.symm.op⟩⟩

instance (P : ObjectProperty Cᵒᵖ) [P.IsTriangulated] : P.unop.IsTriangulated where
  isStableUnderShiftBy n :=
    { le_shift X hX := by
        obtain ⟨m, rfl⟩ : ∃ m, n = -m := ⟨-n , by simp⟩
        exact P.le_shift m _ hX }
  ext₂' := by
    rintro T hT h₁ h₃
    obtain ⟨X, hX, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ (op_distinguished _ hT) h₃ h₁
    exact ⟨Opposite.unop X, hX, ⟨e.symm.unop⟩⟩

lemma trW_of_op (S : ObjectProperty C) [S.IsTriangulated]
    {X Y : C} (f : X ⟶ Y) (hf : S.op.trW f.op) : S.trW f := by
  obtain ⟨Z, a, b, h₁, h₂⟩ := hf
  rw [ObjectProperty.trW_iff']
  exact ⟨_, _, _, Pretriangulated.unop_distinguished _ h₁, h₂⟩

lemma trW_of_unop (S : ObjectProperty Cᵒᵖ) [S.IsTriangulated]
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (hf : S.unop.trW f.unop) : S.trW f := by
  obtain ⟨Z, a, b, h₁, h₂⟩ := hf
  rw [ObjectProperty.trW_iff']
  exact ⟨_, _, _, Pretriangulated.op_distinguished _ h₁, h₂⟩

lemma trW_op_iff (S : ObjectProperty C) [S.IsTriangulated] {X Y : Cᵒᵖ } (f : X ⟶ Y) :
    S.op.trW f ↔ S.trW f.unop :=
  ⟨S.trW_of_op _, S.op.trW_of_unop _⟩

lemma trW_op (S : ObjectProperty C) [S.IsTriangulated] : S.op.trW = S.trW.op := by
  ext X Y f
  apply S.trW_op_iff

end ObjectProperty

end CategoryTheory
