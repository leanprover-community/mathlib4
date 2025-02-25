/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Embedding
import Mathlib.Algebra.Order.Interval.Set.Monoid
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Finset intervals in a successor-predecessor order

This files proves relations between the various finset intervals in a successor/predecessor order.
-/

open Function Order OrderDual

variable {ι α : Type*}

namespace Finset
variable [LinearOrder α] [LocallyFiniteOrder α] [One α]

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a b : α}

lemma Ico_add_one_left_eq_Ioo (a b : α) : Ico (a + 1) b = Ioo a b := by
  simpa [succ_eq_add_one] using Ico_succ_left_eq_Ioo a b

lemma Icc_add_one_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc_of_not_isMax ha b

lemma Ico_add_one_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc_of_not_isMax hb a

lemma Ioo_add_one_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc_of_not_isMax hb a

lemma Ico_add_one_add_one_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc_of_not_isMax hb a

variable [NoMaxOrder α]

lemma Icc_add_one_left_eq_Ioc (a b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc a b

lemma Ico_add_one_right_eq_Icc (a b : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using  Ico_succ_right_eq_Icc a b

lemma Ioo_add_one_right_eq_Ioc (a b : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc a b

lemma Ico_add_one_add_one_eq_Ioc (a b : α) : Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc a b

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}

lemma Ioc_sub_one_right_eq_Ioo (a b : α) : Ioc a (b - 1) = Ioo a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_right_eq_Ioo a b

lemma Icc_sub_one_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico_of_not_isMin hb a

lemma Ioc_sub_one_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc_of_not_isMin ha b

lemma Ioo_sub_one_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc_of_not_isMin ha b

lemma Ioc_sub_one_sub_one_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico_of_not_isMin ha b

variable [NoMinOrder α]

lemma Icc_sub_one_right_eq_Ico (a b : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico a b

lemma Ioc_sub_one_left_eq_Icc (a b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc a b

lemma Ioo_sub_one_left_eq_Ioc (a b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc a b

lemma Ioc_sub_one_sub_one_eq_Ico (a b : α) : Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico a b

end PredSubOrder

section SuccAddPredSubOrder
variable [Add α] [Sub α] [SuccAddOrder α] [PredSubOrder α] [Nontrivial α]

lemma Icc_add_one_sub_one_eq_Ioo (a b : α) : Icc (a + 1) (b - 1) = Ioo a b := by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

end SuccAddPredSubOrder
end Finset
