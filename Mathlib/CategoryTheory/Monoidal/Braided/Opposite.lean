/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# If `C` is braided, so is `Cᵒᵖ`.

Todo: we should also do `Cᵐᵒᵖ`.
-/

open CategoryTheory MonoidalCategory BraidedCategory Opposite

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

instance : BraidedCategory Cᵒᵖ where
  braiding X Y := (β_ (unop Y) (unop X)).op
  braiding_naturality_right X Y Z f := by
    apply Quiver.Hom.unop_inj
    dsimp
    rw [← unop_tensor_unop, ← braiding_naturality, ← unop_tensor_unop]
  braiding_naturality_left f Z := by
    apply Quiver.Hom.unop_inj
    dsimp
    rw [← unop_tensor_unop, ← braiding_naturality, ← unop_tensor_unop]
  hexagon_forward X Y Z := by
    apply Quiver.Hom.unop_inj
    dsimp [op_tensorObj]
    rw [braiding_tensor_left]
    simp? [op_associator] says simp only [op_associator, Iso.op_hom, Iso.symm_hom,
        Quiver.Hom.unop_op, Iso.inv_hom_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    coherence
  hexagon_reverse X Y Z := by
    apply Quiver.Hom.unop_inj
    dsimp [op_tensorObj]
    rw [braiding_tensor_right]
    simp? [op_associator] says simp only [op_associator, Iso.op_inv, Iso.symm_inv,
        Quiver.Hom.unop_op, Iso.hom_inv_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    coherence
