/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Finset intervals in an additive successor-predecessor order

This file proves relations between the various finset intervals in an additive successor/predecessor
order.

## Notes

Please keep in sync with:
* `Mathlib/Algebra/Order/Interval/Set/SuccPred.lean`
* `Mathlib/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Order/Interval/Set/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
-/

open Function Order OrderDual

variable {ι α : Type*}

namespace Finset
variable [LinearOrder α] [One α]

/-! ### Two-sided intervals -/

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a b : α}

/-!
#### Orders possibly with maximal elements

##### Equalities of intervals
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

/-! ##### Inserting into intervals -/

lemma insert_Icc_add_one_left_eq_Icc (h : a ≤ b) : insert a (Icc (a + 1) b) = Icc a b := by
  simpa [succ_eq_add_one] using insert_Icc_succ_left_eq_Icc h

lemma insert_Icc_right_eq_Icc_add_one (h : a ≤ b + 1) :
    insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  simpa [← succ_eq_add_one] using insert_Icc_right_eq_Icc_succ (succ_eq_add_one b ▸ h)

@[deprecated (since := "2025-04-19")]
alias insert_Icc_eq_Icc_add_one_right := insert_Icc_right_eq_Icc_add_one

lemma insert_Ico_right_eq_Ico_add_one_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_of_not_isMax h hb

@[deprecated (since := "2025-04-14")]
alias insert_Ico_right_eq_Ico_add_one_right_of_not_isMax :=
  insert_Ico_right_eq_Ico_add_one_of_not_isMax

lemma insert_Ico_add_one_left_eq_Ico (h : a < b) : insert a (Ico (a + 1) b) = Ico a b := by
  simpa [succ_eq_add_one] using insert_Ico_succ_left_eq_Ico h

lemma insert_Ioc_right_eq_Ioc_add_one_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (b + 1) (Ioc a b) = Ioc a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb

lemma insert_Ioc_add_one_left_eq_Ioc (h : a < b) : insert (a + 1) (Ioc (a + 1) b) = Ioc a b := by
  simpa [succ_eq_add_one] using insert_Ioc_succ_left_eq_Ioc h

/-!
#### Orders with no maximal elements

##### Equalities of intervals
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

/-! ##### Inserting into intervals -/

lemma insert_Ico_right_eq_Ico_add_one (h : a ≤ b) : insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ h

@[deprecated (since := "2025-04-14")]
alias insert_Ico_right_eq_Ico_add_one_right := insert_Ico_right_eq_Ico_add_one

lemma insert_Ioc_right_eq_Ioc_add_one (h : a ≤ b) : insert (b + 1) (Ioc a b) = Ioc a (b + 1) :=
  insert_Ioc_right_eq_Ioc_add_one_of_not_isMax h (not_isMax _)

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}

/-!
#### Orders possibly with minimal elements

##### Equalities of intervals
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

/-! ##### Inserting into intervals -/

lemma insert_Icc_sub_one_right_eq_Icc (h : a ≤ b) : insert b (Icc a (b - 1)) = Icc a b := by
  simpa [pred_eq_sub_one] using insert_Icc_pred_right_eq_Icc h

lemma insert_Icc_left_eq_Icc_sub_one (h : a - 1 ≤ b) :
    insert (a - 1) (Icc a b) = Icc (a - 1) b := by
  simpa [← pred_eq_sub_one] using insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)

@[deprecated (since := "2025-04-19")]
alias insert_Icc_eq_Icc_sub_one_left := insert_Icc_left_eq_Icc_sub_one

lemma insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred_of_not_isMin h ha

@[deprecated (since := "2025-04-14")]
alias insert_Ioc_left_eq_Ioc_sub_one_left_of_not_isMin :=
  insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin

lemma insert_Ioc_sub_one_right_eq_Ioc (h : a < b) : insert b (Ioc a (b - 1)) = Ioc a b := by
  simpa [pred_eq_sub_one] using insert_Ioc_pred_right_eq_Ioc h

lemma insert_Ico_left_eq_Ico_sub_one_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert (a - 1) (Ico a b) = Ico (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ico_left_eq_Ico_pred_of_not_isMin h ha

lemma insert_Ico_sub_one_right_eq_Ico (h : a < b) : insert (b - 1) (Ico a (b - 1)) = Ico a b := by
  simpa [pred_eq_sub_one] using insert_Ico_pred_right_eq_Ico h

/-!
#### Orders with no minimal elements

##### Equalities of intervals
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

/-! ##### Inserting into intervals -/

lemma insert_Ioc_left_eq_Ioc_sub_one (h : a ≤ b) : insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred h

@[deprecated (since := "2025-04-14")]
alias insert_Ioc_left_eq_Ioc_sub_one_left := insert_Ioc_left_eq_Ioc_sub_one

lemma insert_Ico_left_eq_Ico_sub_one (h : a ≤ b) : insert (a - 1) (Ico a b) = Ico (a - 1) b :=
  insert_Ico_left_eq_Ico_sub_one_of_not_isMin h (not_isMin _)

end PredSubOrder

section SuccAddPredSubOrder
variable [Add α] [Sub α] [SuccAddOrder α] [PredSubOrder α] [Nontrivial α]

lemma Icc_add_one_sub_one_eq_Ioo (a b : α) : Icc (a + 1) (b - 1) = Ioo a b := by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

end SuccAddPredSubOrder
end LocallyFiniteOrder

/-! ### One-sided interval towards `⊥` -/

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

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
end LocallyFiniteOrderBot

/-! ### One-sided interval towards `⊤` -/

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

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
end LocallyFiniteOrderTop
end Finset
