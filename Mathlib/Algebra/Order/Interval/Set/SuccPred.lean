/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Order.Interval.Set.SuccPred

/-!
# Set intervals in an additive successor-predecessor order

This file proves relations between the various set intervals in an additive successor/predecessor
order.

## Notes

Please keep in sync with:
* `Mathlib.Algebra.Order.Interval.Finset.SuccPred`
* `Mathlib.Order.Interval.Finset.SuccPred`
* `Mathlib.Order.Interval.Set.SuccPred`

## TODO

Copy over `insert` lemmas from `Mathlib.Order.Interval.Finset.Nat`.
-/

open Function Order OrderDual

variable {ι α : Type*}

namespace Set
variable [LinearOrder α] [One α]

/-! ### Two-sided intervals -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a b : α}

/-!
#### Not `NoMaxOrder`

##### Comparing different intervals
-/

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

/-! ##### Comparing the same intervals -/

lemma insert_Icc_add_one_left_eq_Icc (h : a ≤ b) : insert a (Icc (a + 1) b) = Icc a b := by
  simpa [succ_eq_add_one] using insert_Icc_succ_left_eq_Icc h

lemma insert_Icc_eq_Icc_add_one_right (h : a ≤ b + 1) :
    insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  simpa [← succ_eq_add_one] using insert_Icc_eq_Icc_succ_right (succ_eq_add_one b ▸ h)

lemma insert_Ico_right_eq_Ico_add_one_right_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_right_of_not_isMax h hb

lemma insert_Ico_add_one_left_eq_Ico (h : a < b) : insert a (Ico (a + 1) b) = Ico a b := by
  simpa [succ_eq_add_one] using insert_Ico_succ_left_eq_Ico h

/-!
#### `NoMaxOrder`

##### Comparing different intervals
-/

variable [NoMaxOrder α]

lemma Icc_add_one_left_eq_Ioc (a b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc a b

lemma Ico_add_one_right_eq_Icc (a b : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using  Ico_succ_right_eq_Icc a b

lemma Ioo_add_one_right_eq_Ioc (a b : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc a b

lemma Ico_add_one_add_one_eq_Ioc (a b : α) : Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc a b

/-! ##### Comparing the same intervals -/

lemma insert_Ico_right_eq_Ico_add_one_right (h : a ≤ b) : insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_right h

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}

/-!
#### Not `NoMinOrder`

##### Comparing different intervals
-/

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

/-! ##### Comparing the same intervals -/

lemma insert_Icc_sub_one_right_eq_Icc (h : a ≤ b) : insert b (Icc a (b - 1)) = Icc a b := by
  simpa [pred_eq_sub_one] using insert_Icc_pred_right_eq_Icc h

lemma insert_Icc_eq_Icc_sub_one_left (h : a - 1 ≤ b) :
    insert (a - 1) (Icc a b) = Icc (a - 1) b := by
  simpa [← pred_eq_sub_one] using insert_Icc_eq_Icc_pred_left (pred_eq_sub_one a ▸ h)

lemma insert_Ioc_left_eq_Ioc_sub_one_left_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (pred a) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred_left_of_not_isMin h ha

lemma insert_Ioc_sub_one_right_eq_Ioc (h : a < b) : insert b (Ioc a (pred b)) = Ioc a b := by
  simpa [pred_eq_sub_one] using insert_Ioc_pred_right_eq_Ioc h

/-!
#### `NoMinOrder`

##### Comparing different intervals
-/

variable [NoMinOrder α]

lemma Icc_sub_one_right_eq_Ico (a b : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico a b

lemma Ioc_sub_one_left_eq_Icc (a b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc a b

lemma Ioo_sub_one_left_eq_Ioc (a b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc a b

lemma Ioc_sub_one_sub_one_eq_Ico (a b : α) : Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico a b

/-! ##### Comparing the same intervals -/

lemma insert_Ioc_left_eq_Ioc_sub_one_left (h : a ≤ b) : insert a (Ioc a b) = Ioc (pred a) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred_left h

end PredSubOrder

section SuccAddPredSubOrder
variable [Add α] [Sub α] [SuccAddOrder α] [PredSubOrder α] [Nontrivial α]

lemma Icc_add_one_sub_one_eq_Ioo (a b : α) : Icc (a + 1) (b - 1) = Ioo a b := by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

end SuccAddPredSubOrder

/-! ### One-sided interval towards `⊥` -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {b : α}

lemma Iio_add_one_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic_of_not_isMax hb

variable [NoMaxOrder α]

lemma Iio_add_one_eq_Iic (b : α) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic b

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}

lemma Iic_sub_one_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio_of_not_isMin hb

variable [NoMinOrder α]

lemma Iic_sub_one_eq_Iio (b : α) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio b

end PredSubOrder

/-! ### One-sided interval towards `⊤` -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a : α}

lemma Ici_add_one_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi_of_not_isMax ha

variable [NoMaxOrder α]

lemma Ici_add_one_eq_Ioi (a : α) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi a

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a a : α}

lemma Ioi_sub_one_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici_of_not_isMin ha

variable [NoMinOrder α]

lemma Ioi_sub_one_eq_Ici (a : α) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici a

end PredSubOrder
end Set
