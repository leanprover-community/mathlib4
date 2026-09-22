/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.SuccPred.Basic

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

public section

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

@[to_dual (reorder := a b) Ioc_pred_right_eq_Ioo]
lemma Ico_succ_left_eq_Ioo (a b : α) : Ico (succ a) b = Ioo a b := by
  by_cases ha : IsMax a
  · rw [Ico_eq_empty (ha.mono <| le_succ _).not_lt, Ioo_eq_empty ha.not_lt]
  · ext x
    rw [mem_Ico, mem_Ioo, succ_le_iff_of_not_isMax ha]

@[to_dual Icc_pred_right_eq_Ico_of_not_isMin]
lemma Icc_succ_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (succ a) b = Ioc a b := by
  ext x; rw [mem_Icc, mem_Ioc, succ_le_iff_of_not_isMax ha]

@[to_dual Ioc_pred_left_eq_Icc_of_not_isMin]
lemma Ico_succ_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (succ b) = Icc a b := by
  ext x; rw [mem_Ico, mem_Icc, lt_succ_iff_of_not_isMax hb]

@[to_dual Ioo_pred_left_eq_Ico_of_not_isMin]
lemma Ioo_succ_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (succ b) = Ioc a b := by
  ext x; rw [mem_Ioo, mem_Ioc, lt_succ_iff_of_not_isMax hb]

@[to_dual]
lemma Ico_succ_succ_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (succ a) (succ b) = Ioc a b := by
  rw [Ico_succ_left_eq_Ioo, Ioo_succ_right_eq_Ioc_of_not_isMax hb]

/-! ##### Inserting into intervals -/

@[to_dual insert_Icc_pred_right_eq_Icc]
lemma insert_Icc_succ_left_eq_Icc (h : a ≤ b) : insert a (Icc (succ a) b) = Icc a b := by
  ext x; simp [or_and_left, eq_comm, ← le_iff_eq_or_succ_le]; aesop

@[to_dual insert_Icc_left_eq_Icc_pred]
lemma insert_Icc_right_eq_Icc_succ (h : a ≤ succ b) :
    insert (succ b) (Icc a b) = Icc a (succ b) := by
  ext x; simp [or_and_left, le_succ_iff_eq_or_le]; simp_all

@[to_dual insert_Ioc_left_eq_Ioc_pred_of_not_isMin]
lemma insert_Ico_right_eq_Ico_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (succ b) := by
  rw [Ico_succ_right_of_not_isMax hb, ← Ico_insert_right h]

@[to_dual insert_Ioc_pred_right_eq_Ioc]
lemma insert_Ico_succ_left_eq_Ico (h : a < b) : insert a (Ico (succ a) b) = Ico a b := by
  rw [Ico_succ_left_of_not_isMax h.not_isMax, ← Ioo_insert_left h]

@[to_dual insert_Ico_left_eq_Ico_pred_of_not_isMin]
lemma insert_Ioc_right_eq_Ioc_succ_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (succ b) (Ioc a b) = Ioc a (succ b) := by
  ext x; simp +contextual [or_and_left, le_succ_iff_eq_or_le, lt_succ_of_le_of_not_isMax h hb]

@[to_dual insert_Ico_pred_right_eq_Ico]
lemma insert_Ioc_succ_left_eq_Ioc (h : a < b) : insert (succ a) (Ioc (succ a) b) = Ioc a b := by
  rw [Ioc_insert_left (succ_le_of_lt h), Icc_succ_left_of_not_isMax h.not_isMax]

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

@[to_dual (reorder := a b) Icc_pred_right_eq_Ico]
lemma Icc_succ_left_eq_Ioc (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_eq_Ioc_of_not_isMax (not_isMax _) _

@[to_dual (reorder := a b) Ioc_pred_left_eq_Icc]
lemma Ico_succ_right_eq_Icc (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_eq_Icc_of_not_isMax (not_isMax _) _

@[to_dual (reorder := a b) Ioo_pred_left_eq_Ico]
lemma Ioo_succ_right_eq_Ioc (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_eq_Ioc_of_not_isMax (not_isMax _) _

@[to_dual (reorder := a b)]
lemma Ico_succ_succ_eq_Ioc (a b : α) : Ico (succ a) (succ b) = Ioc a b :=
  Ico_succ_succ_eq_Ioc_of_not_isMax (not_isMax _) _

/-! ##### Inserting into intervals -/

@[to_dual insert_Ioc_left_eq_Ioc_pred]
lemma insert_Ico_right_eq_Ico_succ (h : a ≤ b) : insert b (Ico a b) = Ico a (succ b) :=
  insert_Ico_right_eq_Ico_succ_of_not_isMax h (not_isMax _)

@[to_dual insert_Ico_left_eq_Ico_pred]
lemma insert_Ioc_right_eq_Ioc_succ (h : a ≤ b) : insert (succ b) (Ioc a b) = Ioc a (succ b) :=
  insert_Ioc_right_eq_Ioc_succ_of_not_isMax h (not_isMax _)

@[deprecated (since := "2026-09-02")]
alias Ioo_pred_left_eq_Ioc_of_not_isMin := Ioo_pred_left_eq_Ico_of_not_isMin

@[deprecated (since := "2026-09-02")] alias Ioo_pred_left_eq_Ioc := Ioo_pred_left_eq_Ico

end SuccOrder


section SuccPredOrder
variable [SuccOrder α] [PredOrder α] [Nontrivial α]

@[to_dual self]
lemma Icc_succ_pred_eq_Ioo (a b : α) : Icc (succ a) (pred b) = Ioo a b := by
  by_cases hb : IsMin b
  · rw [Icc_eq_empty, Ioo_eq_empty hb.not_lt]
    exact fun h ↦ not_isMin_succ _ <| hb.mono <| h.trans <| pred_le _
  · rw [Icc_pred_right_eq_Ico_of_not_isMin hb, Ico_succ_left_eq_Ioo]

end SuccPredOrder

/-! ### One-sided intervals -/

section SuccOrder
variable [SuccOrder α] {a : α}

@[to_dual]
lemma Iio_succ_eq_Iic_of_not_isMax (hb : ¬ IsMax a) : Iio (succ a) = Iic a := by
  ext x; rw [mem_Iio, mem_Iic, lt_succ_iff_of_not_isMax hb]

@[to_dual]
lemma Ici_succ_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (succ a) = Ioi a := by
  ext x; rw [mem_Ici, mem_Ioi, succ_le_iff_of_not_isMax ha]

variable [NoMaxOrder α]

@[to_dual]
lemma Iio_succ_eq_Iic (a : α) : Iio (succ a) = Iic a := Iio_succ_eq_Iic_of_not_isMax (not_isMax _)

@[to_dual]
lemma Ici_succ_eq_Ioi (a : α) : Ici (succ a) = Ioi a := Ici_succ_eq_Ioi_of_not_isMax (not_isMax _)

end SuccOrder
end Set
