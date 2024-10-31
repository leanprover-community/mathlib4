/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
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

namespace CategoryTheory.BraidedCategory

@[simp] lemma unop_tensor_μ {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (X Y W Z : Cᵒᵖ) :
    (tensor_μ X W Y Z).unop = tensor_μ X.unop Y.unop W.unop Z.unop := by
  simp only [unop_tensorObj, tensor_μ, unop_comp, unop_inv_associator, unop_whiskerLeft,
    unop_hom_associator, unop_whiskerRight, unop_hom_braiding, Category.assoc]

@[simp] lemma op_tensor_μ {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (X Y W Z : C) :
    (tensor_μ X W Y Z).op = tensor_μ (op X) (op Y) (op W) (op Z) := by
  simp only [op_tensorObj, tensor_μ, op_comp, op_inv_associator, op_whiskerLeft, op_hom_associator,
    op_whiskerRight, op_hom_braiding, Category.assoc]

end CategoryTheory.BraidedCategory
