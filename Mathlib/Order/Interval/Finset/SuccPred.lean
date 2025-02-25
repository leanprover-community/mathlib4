/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Embedding
import Mathlib.Algebra.Order.Interval.Set.Monoid
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Order.Interval.Finset.Basic

open Order

namespace Finset
variable {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]

section SuccOrder
variable [SuccOrder α] {a b : α}

lemma Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) b = Ioo a b := by
  by_cases ha : IsMax a
  · rw [Ico_eq_empty (ha.mono <| le_succ _).not_lt, Ioo_eq_empty ha.not_lt]
  · ext x
    rw [mem_Ico, mem_Ioo, succ_le_iff_of_not_isMax ha]

lemma Icc_succ_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b := by
  ext x; rw [mem_Icc, mem_Ioc, succ_le_iff_of_not_isMax ha]

lemma Ico_succ_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b := by
  ext x; rw [mem_Ico, mem_Icc, lt_succ_iff_of_not_isMax hb]

lemma Ioo_succ_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b := by
  ext x; rw [mem_Ioo, mem_Ioc, lt_succ_iff_of_not_isMax hb]

lemma Ico_succ_succ_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (succ a) (succ b) = Ioc a b := by
  rw [Ico_succ_left_eq_Ioo, Ioo_succ_right_eq_Ioc_of_not_isMax hb]

variable [NoMaxOrder α]

lemma Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_eq_Ioc_of_not_isMax (not_isMax _) _

lemma Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_eq_Icc_of_not_isMax (not_isMax _) _

lemma Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_eq_Ioc_of_not_isMax (not_isMax _) _

lemma Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b :=
  Ico_succ_succ_eq_Ioc_of_not_isMax (not_isMax _) _

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

lemma Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred b) = Ioo a b := by
  by_cases hb : IsMin b
  · rw [Ioc_eq_empty (hb.mono <| pred_le _).not_lt, Ioo_eq_empty hb.not_lt]
  · ext x
    rw [mem_Ioc, mem_Ioo, le_pred_iff_of_not_isMin hb]

lemma Icc_pred_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b := by
  ext x; rw [mem_Icc, mem_Ico, le_pred_iff_of_not_isMin hb]

lemma Ioc_pred_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) b = Icc a b := by
  ext x; rw [mem_Ioc, mem_Icc, pred_lt_iff_of_not_isMin ha]

lemma Ioo_pred_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b := by
  ext x; rw [mem_Ioo, mem_Ico, pred_lt_iff_of_not_isMin ha]

lemma Ioc_pred_pred_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (pred a) (pred b) = Ico a b := by
  rw [Ioc_pred_right_eq_Ioo, Ioo_pred_left_eq_Ioc_of_not_isMin ha]

variable [NoMinOrder α]

lemma Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_eq_Ico_of_not_isMin (not_isMin _) _

lemma Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_eq_Icc_of_not_isMin (not_isMin _) _

lemma Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_eq_Ioc_of_not_isMin (not_isMin _) _

lemma Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b :=
  Ioc_pred_pred_eq_Ico_of_not_isMin (not_isMin _) _

end PredOrder

section SuccPredOrder
variable [SuccOrder α] [PredOrder α] [Nontrivial α]

lemma Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) (pred b) = Ioo a b := by
  by_cases hb : IsMin b
  · rw [Icc_eq_empty, Ioo_eq_empty hb.not_lt]
    exact fun h ↦ not_isMin_succ _ <| hb.mono <| h.trans <| pred_le _
  · rw [Icc_pred_right_eq_Ico_of_not_isMin hb, Ico_succ_left_eq_Ioo]

end SuccPredOrder
end Finset
