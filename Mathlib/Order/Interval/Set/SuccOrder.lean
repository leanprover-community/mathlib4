/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.LatticeIntervals
import Mathlib.Order.SuccPred.Basic

/-!
# Successors in intervals

If `j` is an element of a partially ordered set equipped
with a successor function, then for any element `i : Set.Iic j`
which is not the maximum, we have `↑(Order.succ i) = Order.succ ↑i`.

-/

namespace Set

variable {J : Type*} [PartialOrder J]

lemma Iic.coe_succ_of_not_isMax
    [SuccOrder J] {j : J} {i : Set.Iic j} (hi : ¬ IsMax i) :
    (Order.succ i).1 = Order.succ i.1 := by
  rw [coe_succ_of_mem]
  apply Order.succ_le_of_lt
  exact lt_of_le_of_ne (α := Set.Iic j) le_top (by simpa using hi)

lemma Iic.succ_eq_of_not_isMax
    [SuccOrder J] {j : J} {i : Set.Iic j} (hi : ¬ IsMax i) :
    Order.succ i = ⟨Order.succ i.1, by
      rw [← coe_succ_of_not_isMax hi]
      apply Subtype.coe_prop⟩ := by
  ext
  simp only [coe_succ_of_not_isMax hi]

lemma Ici.coe_pred_of_not_isMin
    [PredOrder J] {j : J} {i : Set.Ici j} (hi : ¬ IsMin i) :
    (Order.pred i).1 = Order.pred i.1 := by
  rw [coe_pred_of_mem]
  apply Order.le_pred_of_lt
  exact lt_of_le_of_ne (α := Set.Ici j) bot_le (Ne.symm (by simpa using hi))

lemma Ici.pred_eq_of_not_isMin
    [PredOrder J] {j : J} {i : Set.Ici j} (hi : ¬ IsMin i) :
    Order.pred i = ⟨Order.pred i.1, by
      rw [← coe_pred_of_not_isMin hi]
      apply Subtype.coe_prop⟩ := by
  ext
  simp only [coe_pred_of_not_isMin hi]

end Set
