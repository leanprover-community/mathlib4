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
* `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Algebra/Order/Interval/Set/SuccPred.lean`
* `Mathlib/Order/Interval/Finset/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
-/

assert_not_exists MonoidWithZero

open Order

namespace Set
variable {α : Type*} [LinearOrder α]

/-! ### Two-sided intervals -/

section SuccOrder
variable [SuccOrder α] {a b : α}

/-!
#### Orders possibly with maximal elements

##### Equalities of intervals
-/

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

/-! ##### Inserting into intervals -/

lemma insert_Icc_succ_left_eq_Icc (h : a ≤ b) : insert a (Icc (succ a) b) = Icc a b := by
  ext x; simp [or_and_left, eq_comm, ← le_iff_eq_or_succ_le]; aesop

lemma insert_Icc_right_eq_Icc_succ (h : a ≤ succ b) :
    insert (succ b) (Icc a b) = Icc a (succ b) := by
  ext x; simp [or_and_left, le_succ_iff_eq_or_le]; aesop

@[deprecated (since := "2025-04-19")]
alias insert_Icc_eq_Icc_succ_right := insert_Icc_right_eq_Icc_succ

lemma insert_Ico_right_eq_Ico_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (succ b) := by
  rw [Ico_succ_right_of_not_isMax hb, ← Ico_insert_right h]

@[deprecated (since := "2025-04-14")]
alias insert_Ico_right_eq_Ico_succ_right_of_not_isMax := insert_Ico_right_eq_Ico_succ_of_not_isMax

lemma insert_Ico_succ_left_eq_Ico (h : a < b) : insert a (Ico (succ a) b) = Ico a b := by
  rw [Ico_succ_left_of_not_isMax h.not_isMax, ← Ioo_insert_left h]

lemma insert_Ioc_right_eq_Ioc_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (succ b) (Ioc a b) = Ioc a (succ b) := by
  ext x; simp +contextual [or_and_left, le_succ_iff_eq_or_le, lt_succ_of_le_of_not_isMax h hb]

lemma insert_Ioc_succ_left_eq_Ioc (h : a < b) : insert (succ a) (Ioc (succ a) b) = Ioc a b := by
  rw [Ioc_insert_left (succ_le_of_lt h), Icc_succ_left_of_not_isMax h.not_isMax]

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

lemma Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_eq_Ioc_of_not_isMax (not_isMax _) _

lemma Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_eq_Icc_of_not_isMax (not_isMax _) _

lemma Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_eq_Ioc_of_not_isMax (not_isMax _) _

lemma Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b :=
  Ico_succ_succ_eq_Ioc_of_not_isMax (not_isMax _) _

/-! ##### Inserting into intervals -/

lemma insert_Ico_right_eq_Ico_succ (h : a ≤ b) : insert b (Ico a b) = Ico a (succ b) :=
  insert_Ico_right_eq_Ico_succ_of_not_isMax h (not_isMax _)

@[deprecated (since := "2025-04-14")]
alias insert_Ico_right_eq_Ico_succ_right := insert_Ico_right_eq_Ico_succ

lemma insert_Ioc_right_eq_Ioc_succ (h : a ≤ b) : insert (succ b) (Ioc a b) = Ioc a (succ b) :=
  insert_Ioc_right_eq_Ioc_succ_of_not_isMax h (not_isMax _)

end SuccOrder

section PredOrder
variable [PredOrder α] {a b : α}

/-!
#### Orders possibly with minimal elements

##### Equalities of intervals
-/

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

/-! ##### Inserting into intervals -/

lemma insert_Icc_pred_right_eq_Icc (h : a ≤ b) : insert b (Icc a (pred b)) = Icc a b := by
  ext x; simp [or_and_left, eq_comm (a := b), ← le_iff_eq_or_le_pred]; aesop

lemma insert_Icc_left_eq_Icc_pred (h : pred a ≤ b) :
    insert (pred a) (Icc a b) = Icc (pred a) b := by
  ext x; simp [or_and_left, pred_le_iff_eq_or_le]; aesop

@[deprecated (since := "2025-04-19")]
alias insert_Icc_eq_Icc_pred_left := insert_Icc_left_eq_Icc_pred

lemma insert_Ioc_left_eq_Ioc_pred_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (pred a) b := by
  rw [Ioc_pred_left_of_not_isMin ha, Ioc_insert_left h]

@[deprecated (since := "2025-04-14")]
alias insert_Ioc_left_eq_Ioc_pred_left_of_not_isMin := insert_Ioc_left_eq_Ioc_pred_of_not_isMin

lemma insert_Ioc_pred_right_eq_Ioc (h : a < b) : insert b (Ioc a (pred b)) = Ioc a b := by
  rw [Ioc_pred_right_of_not_isMin h.not_isMin, Ioo_insert_right h]

lemma insert_Ico_left_eq_Ico_pred_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert (pred a) (Ico a b) = Ico (pred a) b := by
  ext x; simp +contextual [or_and_left, pred_le_iff_eq_or_le, pred_lt_of_not_isMin_of_le ha h]

lemma insert_Ico_pred_right_eq_Ico (h : a < b) : insert (pred b) (Ico a (pred b)) = Ico a b := by
  rw [Ico_insert_right (le_pred_of_lt h), Icc_pred_right_of_not_isMin h.not_isMin]

/-!
#### Orders with no minimal elements

##### Equalities of intervals
-/

variable [NoMinOrder α]

lemma Icc_pred_right_eq_Ico (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_eq_Ico_of_not_isMin (not_isMin _) _

lemma Ioc_pred_left_eq_Icc (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_eq_Icc_of_not_isMin (not_isMin _) _

lemma Ioo_pred_left_eq_Ioc (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_eq_Ioc_of_not_isMin (not_isMin _) _

lemma Ioc_pred_pred_eq_Ico (a b : α) : Ioc (pred a) (pred b) = Ico a b :=
  Ioc_pred_pred_eq_Ico_of_not_isMin (not_isMin _) _

/-! ##### Inserting into intervals -/

lemma insert_Ioc_left_eq_Ioc_pred (h : a ≤ b) : insert a (Ioc a b) = Ioc (pred a) b :=
  insert_Ioc_left_eq_Ioc_pred_of_not_isMin h (not_isMin _)

@[deprecated (since := "2025-04-14")]
alias insert_Ioc_left_eq_Ioc_pred_left := insert_Ioc_left_eq_Ioc_pred

lemma insert_Ico_left_eq_Ico_pred (h : a ≤ b) : insert (pred a) (Ico a b) = Ico (pred a) b :=
  insert_Ico_left_eq_Ico_pred_of_not_isMin h (not_isMin _)

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
