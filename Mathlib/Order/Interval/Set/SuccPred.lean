/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.SuccPred.Basic

/-!
# Set intervals in a successor-predecessor order

This file proves relations between the various set intervals in a successor/predecessor order.

## Notes

Please keep in sync with:
* `Mathlib.Algebra.Order.Interval.Finset.SuccPred`
* `Mathlib.Algebra.Order.Interval.Set.SuccPred`
* `Mathlib.Order.Interval.Finset.SuccPred`

## TODO

Copy over `insert` lemmas from `Mathlib.Order.Interval.Finset.Nat`.
-/

assert_not_exists MonoidWithZero

open Order

namespace Set
variable {α : Type*} [LinearOrder α]

/-! ### Two-sided intervals -/

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

/-! ### One-sided interval towards `⊥` -/

section SuccOrder
variable [SuccOrder α] {b : α}

lemma Iio_succ_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (succ b) = Iic b := by
  ext x; rw [mem_Iio, mem_Iic, lt_succ_iff_of_not_isMax hb]

variable [NoMaxOrder α]

lemma Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b := Iio_succ_eq_Iic_of_not_isMax (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

lemma Iic_pred_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (pred b) = Iio b := by
  ext x; rw [mem_Iic, mem_Iio, le_pred_iff_of_not_isMin hb]

variable [NoMinOrder α]

lemma Iic_pred_eq_Iio (b : α) : Iic (pred b) = Iio b := Iic_pred_eq_Iio_of_not_isMin (not_isMin _)

end PredOrder

/-! ### One-sided interval towards `⊤` -/

section SuccOrder
variable [SuccOrder α] {a : α}

lemma Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (succ a) = Ioi a := by
  ext x; rw [mem_Ici, mem_Ioi, succ_le_iff_of_not_isMax ha]

variable [NoMaxOrder α]

lemma Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a := Ici_succ_eq_Ioi_of_not_isMax (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a a : α}

lemma Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (pred a) = Ici a := by
  ext x; rw [mem_Ioi, mem_Ici, pred_lt_iff_of_not_isMin ha]

variable [NoMinOrder α]

lemma Ioi_pred_eq_Ici (a : α) : Ioi (pred a) = Ici a := Ioi_pred_eq_Ici_of_not_isMin (not_isMin _)

end PredOrder
end Set
