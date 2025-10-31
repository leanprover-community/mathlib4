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
* `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Algebra/Order/Interval/Set/SuccPred.lean`
* `Mathlib/Order/Interval/Set/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
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

/-!
#### Orders possibly with maximal elements

##### Equalities of intervals
-/

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

/-! ##### Inserting into intervals -/

lemma insert_Icc_succ_left_eq_Icc (h : a ≤ b) : insert a (Icc (succ a) b) = Icc a b :=
  coe_injective <| by simpa using Set.insert_Icc_succ_left_eq_Icc h

lemma insert_Icc_right_eq_Icc_succ (h : a ≤ succ b) : insert (succ b) (Icc a b) = Icc a (succ b) :=
  coe_injective <| by simpa using Set.insert_Icc_right_eq_Icc_succ h

lemma insert_Ico_right_eq_Ico_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (succ b) :=
  coe_injective <| by simpa using Set.insert_Ico_right_eq_Ico_succ_of_not_isMax h hb

lemma insert_Ico_succ_left_eq_Ico (h : a < b) : insert a (Ico (succ a) b) = Ico a b :=
  coe_injective <| by simpa using Set.insert_Ico_succ_left_eq_Ico h

lemma insert_Ioc_right_eq_Ioc_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (succ b) (Ioc a b) = Ioc a (succ b) :=
  coe_injective <| by simpa using Set.insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb

lemma insert_Ioc_succ_left_eq_Ioc (h : a < b) : insert (succ a) (Ioc (succ a) b) = Ioc a b :=
  coe_injective <| by simpa using Set.insert_Ioc_succ_left_eq_Ioc h

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

lemma Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b := coe_injective <| by simp
lemma Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b := coe_injective <| by simp
lemma Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b := coe_injective <| by simp
lemma Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b := coe_injective <| by simp

/-! ##### Inserting into intervals -/

lemma insert_Ico_right_eq_Ico_succ (h : a ≤ b) : insert b (Ico a b) = Ico a (succ b) :=
  coe_injective <| by simpa using Set.insert_Ico_right_eq_Ico_succ h

lemma insert_Ioc_right_eq_Ioc_succ (h : a ≤ b) : insert (succ b) (Ioc a b) = Ioc a (succ b) :=
  coe_injective <| by simpa using Set.insert_Ioc_right_eq_Ioc_succ h

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

/-!
#### Orders possibly with minimal elements

##### Equalities of intervals
-/

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

/-! ##### Inserting into intervals -/

lemma insert_Icc_pred_right_eq_Icc (h : a ≤ b) : insert b (Icc a (pred b)) = Icc a b :=
  coe_injective <| by simpa using Set.insert_Icc_pred_right_eq_Icc h

lemma insert_Icc_left_eq_Icc_pred (h : pred a ≤ b) : insert (pred a) (Icc a b) = Icc (pred a) b :=
  coe_injective <| by simpa using Set.insert_Icc_left_eq_Icc_pred h

lemma insert_Ioc_left_eq_Ioc_pred_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (pred a) b :=
  coe_injective <| by simpa using Set.insert_Ioc_left_eq_Ioc_pred_of_not_isMin h ha

lemma insert_Ioc_pred_right_eq_Ioc (h : a < b) : insert b (Ioc a (pred b)) = Ioc a b :=
  coe_injective <| by simpa using Set.insert_Ioc_pred_right_eq_Ioc h

lemma insert_Ico_left_eq_Ico_pred_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert (pred a) (Ico a b) = Ico (pred a) b :=
  coe_injective <| by simpa using Set.insert_Ico_left_eq_Ico_pred_of_not_isMin h ha

lemma insert_Ico_pred_right_eq_Ico (h : a < b) : insert (pred b) (Ico a (pred b)) = Ico a b :=
  coe_injective <| by simpa using Set.insert_Ico_pred_right_eq_Ico h

/-!
#### Orders with no minimal elements

##### Equalities of intervals
-/

variable [NoMinOrder α]

lemma Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b := coe_injective <| by simp
lemma Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b := coe_injective <| by simp
lemma Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b := coe_injective <| by simp
lemma Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b := coe_injective <| by simp

/-! ##### Inserting into intervals -/

lemma insert_Ioc_left_eq_Ioc_pred (h : a ≤ b) : insert a (Ioc a b) = Ioc (pred a) b :=
  coe_injective <| by simpa using Set.insert_Ioc_left_eq_Ioc_pred h

lemma insert_Ico_left_eq_Ico_pred (h : a ≤ b) : insert (pred a) (Ico a b) = Ico (pred a) b :=
  insert_Ico_left_eq_Ico_pred_of_not_isMin h (not_isMin _)

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
