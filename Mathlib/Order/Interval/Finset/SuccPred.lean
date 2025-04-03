/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.SuccPred

/-!
# Finset intervals in a successor-predecessor order

This file proves relations between the various finset intervals in a successor/predecessor order.

## Notes

Please keep in sync with:
* `Mathlib.Algebra.Order.Interval.Finset.SuccPred`
* `Mathlib.Algebra.Order.Interval.Set.SuccPred`
* `Mathlib.Order.Interval.Set.SuccPred`

## TODO

Copy over `insert` lemmas from `Mathlib.Order.Interval.Finset.Nat`.
-/

assert_not_exists MonoidWithZero

open Order

namespace Finset
variable {α : Type*} [LinearOrder α]

/-! ### Two-sided intervals -/

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

section SuccOrder
variable [SuccOrder α] {a b : α}

lemma Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) b = Ioo a b :=
  coe_injective <| by simpa using Set.Ico_succ_left_eq_Ioo _ _

lemma Icc_succ_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b :=
  coe_injective <| by simpa using Set.Icc_succ_left_eq_Ioc_of_not_isMax ha _

lemma Ico_succ_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b :=
  coe_injective <| by simpa using Set.Ico_succ_right_eq_Icc_of_not_isMax hb _

lemma Ioo_succ_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b :=
  coe_injective <| by simpa using Set.Ioo_succ_right_eq_Ioc_of_not_isMax hb _

lemma Ico_succ_succ_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (succ a) (succ b) = Ioc a b :=
  coe_injective <| by simpa using Set.Ico_succ_succ_eq_Ioc_of_not_isMax hb _

variable [NoMaxOrder α]

lemma Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b := coe_injective <| by simp
lemma Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b := coe_injective <| by simp
lemma Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b := coe_injective <| by simp
lemma Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b := coe_injective <| by simp

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

lemma Ioc_pred_right_eq_Ioo (a b : α) : Ioc a (pred b) = Ioo a b :=
  coe_injective <| by simpa using Set.Ioc_pred_right_eq_Ioo _ _

lemma Icc_pred_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (pred b) = Ico a b :=
  coe_injective <| by simpa using Set.Icc_pred_right_eq_Ico_of_not_isMin hb _

lemma Ioc_pred_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (pred a) b = Icc a b :=
  coe_injective <| by simpa using Set.Ioc_pred_left_eq_Icc_of_not_isMin ha _

lemma Ioo_pred_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (pred a) b = Ico a b :=
  coe_injective <| by simpa using Set.Ioo_pred_left_eq_Ioc_of_not_isMin ha _

lemma Ioc_pred_pred_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (pred a) (pred b) = Ico a b :=
  coe_injective <| by simpa using Set.Ioc_pred_pred_eq_Ico_of_not_isMin ha _

variable [NoMinOrder α]

lemma Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b := coe_injective <| by simp
lemma Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b := coe_injective <| by simp
lemma Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b := coe_injective <| by simp
lemma Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b := coe_injective <| by simp

end PredOrder

section SuccPredOrder
variable [SuccOrder α] [PredOrder α] [Nontrivial α]

lemma Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) (pred b) = Ioo a b :=
  coe_injective <| by simpa using Set.Icc_succ_pred_eq_Ioo _ _

end SuccPredOrder
end LocallyFiniteOrder

/-! ### One-sided interval towards `⊥` -/

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

section SuccOrder
variable [SuccOrder α] {b : α}

lemma Iio_succ_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (succ b) = Iic b :=
  coe_injective <| by simpa using Set.Iio_succ_eq_Iic_of_not_isMax hb

variable [NoMaxOrder α]

lemma Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b := coe_injective <| by simp

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

lemma Iic_pred_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (pred b) = Iio b :=
  coe_injective <| by simpa using Set.Iic_pred_eq_Iio_of_not_isMin hb

variable [NoMinOrder α]

lemma Iic_pred_eq_Iio (b : α) : Iic (pred b) = Iio b := coe_injective <| by simp

end PredOrder
end LocallyFiniteOrderBot

/-! ### One-sided interval towards `⊤` -/

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

section SuccOrder
variable [SuccOrder α] {a : α}

lemma Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (succ a) = Ioi a :=
  coe_injective <| by simpa using Set.Ici_succ_eq_Ioi_of_not_isMax ha

variable [NoMaxOrder α]

lemma Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a := coe_injective <| by simp

end SuccOrder

section PredOrder
variable [PredOrder α] {a a : α}

lemma Ioi_pred_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (pred a) = Ici a :=
  coe_injective <| by simpa using Set.Ioi_pred_eq_Ici_of_not_isMin ha

variable [NoMinOrder α]

lemma Ioi_pred_eq_Ici (a : α) : Ioi (pred a) = Ici a := coe_injective <| by simp

end PredOrder
end LocallyFiniteOrderTop
end Finset
