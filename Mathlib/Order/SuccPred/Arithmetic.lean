/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Order.SuccPred.Basic

/-!
# Interaction between successors and arithmetic

We define the `SuccAddOrder` and `PredSubOrder` typeclasses, for orders satisfying `succ x = x + 1`
and `pred x = x - 1` respectively. This allows us to transfer the API for successors and
predecessors into these common arithmetical forms.
-/

/-- A typeclass for `succ x = x + 1`. -/
class SuccAddOrder (α : Type*) [Preorder α] [Add α] [One α] extends SuccOrder α where
  succ_eq_add_one (x : α) : succ x = x + 1

/-- A typeclass for `pred x = x - 1`. -/
class PredSubOrder (α : Type*) [Preorder α] [Sub α] [One α] extends PredOrder α where
  pred_eq_sub_one (x : α) : pred x = x - 1

variable {α : Type*} {x y : α}

namespace Order

section Preorder

variable [Preorder α]

theorem succ_eq_add_one [Add α] [One α] [SuccAddOrder α] (x : α) : succ x = x + 1 :=
  SuccAddOrder.succ_eq_add_one x

theorem pred_eq_sub_one [Sub α] [One α] [PredSubOrder α] (x : α) : pred x = x - 1 :=
  PredSubOrder.pred_eq_sub_one x

theorem add_one_le_of_lt [Add α] [One α] [SuccAddOrder α] (h : x < y) : x + 1 ≤ y := by
  rw [← succ_eq_add_one]
  exact succ_le_of_lt h

theorem le_sub_one_of_lt [Sub α] [One α] [PredSubOrder α] (h : x < y) : x ≤ y - 1 := by
  rw [← pred_eq_sub_one]
  exact le_pred_of_lt h

theorem add_one_le_iff_of_not_isMax [Add α] [One α] [SuccAddOrder α] (hx : ¬ IsMax x) :
    x + 1 ≤ y ↔ x < y := by
  rw [← succ_eq_add_one, succ_le_iff_of_not_isMax hx]

theorem le_sub_one_iff_of_not_isMin [Sub α] [One α] [PredSubOrder α] (hy : ¬ IsMin y) :
    x ≤ y - 1 ↔ x < y := by
  rw [← pred_eq_sub_one, le_pred_iff_of_not_isMin hy]

theorem add_one_le_iff [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] : x + 1 ≤ y ↔ x < y :=
  add_one_le_iff_of_not_isMax (not_isMax x)

theorem le_sub_one_iff [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] : x ≤ y - 1 ↔ x < y :=
  le_sub_one_iff_of_not_isMin (not_isMin y)

@[simp]
theorem succ_zero [AddZeroClass α] [One α] [SuccAddOrder α] : succ (0 : α) = 1 := by
  rw [succ_eq_add_one, zero_add]

@[simp]
theorem pred_zero [SubNegMonoid α] [One α] [PredSubOrder α] : pred (0 : α) = -1 := by
  rw [pred_eq_sub_one, zero_sub]

theorem succ_one [AddMonoidWithOne α] [SuccAddOrder α] : succ (1 : α) = 2 := by
  rw [succ_eq_add_one, one_add_one_eq_two]

@[simp]
theorem pred_one [AddGroup α] [One α] [PredSubOrder α] : pred (1 : α) = 0 := by
  rw [pred_eq_sub_one, sub_self]

theorem add_succ [AddSemigroup α] [One α] [SuccAddOrder α] (x y : α) :
    x + succ y = succ (x + y) := by
  rw [succ_eq_add_one, succ_eq_add_one, add_assoc]

theorem add_pred [AddGroup α] [One α] [PredSubOrder α] (x y : α) :
    x + pred y = pred (x + y) := by
  rw [pred_eq_sub_one, pred_eq_sub_one, add_sub]

theorem succ_add [AddCommSemigroup α] [One α] [SuccAddOrder α] (x y : α) :
    succ x + y = succ (x + y) := by
  rw [add_comm, add_succ, add_comm]

theorem pred_add [AddCommGroup α] [One α] [PredSubOrder α] (x y : α) :
    pred x + y = pred (x + y) := by
  rw [add_comm, add_pred, add_comm]

theorem natCast_succ [AddMonoidWithOne α] [SuccAddOrder α] (n : ℕ) : n.succ = succ (n : α) := by
  cases n with
  | zero => rw [Nat.cast_zero, succ_zero, Nat.cast_one]
  | succ n => rw [succ_eq_add_one, Nat.cast_add_one, Nat.cast_succ]

@[simp]
theorem wcovBy_add_one [Add α] [One α] [SuccAddOrder α] (x : α) : x ⩿ x + 1 := by
  rw [← succ_eq_add_one]
  exact wcovBy_succ x

@[simp]
theorem sub_one_wcovBy [Sub α] [One α] [PredSubOrder α] (x : α) : x - 1 ⩿ x := by
  rw [← pred_eq_sub_one]
  exact pred_wcovBy x

@[simp]
theorem covBy_add_one [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] (x : α) : x ⋖ x + 1 := by
  rw [← succ_eq_add_one]
  exact covBy_succ x

@[simp]
theorem sub_one_covBy [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] (x : α) : x - 1 ⋖ x := by
  rw [← pred_eq_sub_one]
  exact pred_covBy x

theorem succ_iterate [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : ℕ) :
    succ^[n] x = x + n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, ← add_succ, succ_eq_add_one, Nat.cast_one]

theorem pred_iterate [AddCommGroupWithOne α] [PredSubOrder α] (x : α) (n : ℕ) :
    pred^[n] x = x - n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, sub_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, pred_eq_sub_one, Nat.cast_one, sub_sub]

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem not_isMax_zero [Zero α] [One α] [ZeroLEOneClass α] [NeZero (1 : α)] : ¬ IsMax (0 : α) := by
  rw [not_isMax_iff]
  exact ⟨1, one_pos⟩

theorem one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : 1 ≤ x ↔ 0 < x := by
  rw [← succ_zero, succ_le_iff_of_not_isMax not_isMax_zero]

theorem covBy_iff_add_one_eq [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    x ⋖ y ↔ x + 1 = y := by
  rw [← succ_eq_add_one]
  exact succ_eq_iff_covBy.symm

theorem covBy_iff_eq_sub_one [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] :
    x ⋖ y ↔ y - 1 = x := by
  rw [← pred_eq_sub_one]
  exact pred_eq_iff_covBy.symm

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem le_of_lt_add_one [Add α] [One α] [SuccAddOrder α] (h : x < y + 1) : x ≤ y := by
  rw [← succ_eq_add_one] at h
  exact le_of_lt_succ h

theorem le_of_sub_one_lt [Sub α] [One α] [PredSubOrder α] (h : x - 1 < y) : x ≤ y := by
  rw [← pred_eq_sub_one] at h
  exact le_of_pred_lt h

theorem lt_add_one_iff_of_not_isMax [Add α] [One α] [SuccAddOrder α] (hy : ¬ IsMax y) :
    x < y + 1 ↔ x ≤ y := by
  rw [← succ_eq_add_one, lt_succ_iff_of_not_isMax hy]

theorem sub_one_lt_iff_of_not_isMin [Sub α] [One α] [PredSubOrder α] (hx : ¬ IsMin x) :
    x - 1 < y ↔ x ≤ y := by
  rw [← pred_eq_sub_one, pred_lt_iff_of_not_isMin hx]

theorem lt_add_one_iff [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] : x < y + 1 ↔ x ≤ y :=
  lt_add_one_iff_of_not_isMax (not_isMax y)

theorem sub_one_lt_iff [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] : x - 1 < y ↔ x ≤ y :=
  sub_one_lt_iff_of_not_isMin (not_isMin x)

theorem lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : x < 1 ↔ x ≤ 0 := by
  rw [← succ_zero, lt_succ_iff_of_not_isMax not_isMax_zero]

end LinearOrder

end Order
