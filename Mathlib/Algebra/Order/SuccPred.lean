/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Yaël Dillies
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

## Todo

In the future, we will make `x + 1` and `x - 1` the `simp`-normal forms for `succ x` and `pred x`
respectively. This will require a refactor of `Ordinal` first, as the `simp`-normal form is
currently set the other way around.
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

section Add

variable [Add α] [One α] [SuccAddOrder α]

theorem succ_eq_add_one (x : α) : succ x = x + 1 :=
  SuccAddOrder.succ_eq_add_one x

theorem add_one_le_of_lt (h : x < y) : x + 1 ≤ y := by
  rw [← succ_eq_add_one]
  exact succ_le_of_lt h

theorem add_one_le_iff_of_not_isMax (hx : ¬ IsMax x) : x + 1 ≤ y ↔ x < y := by
  rw [← succ_eq_add_one, succ_le_iff_of_not_isMax hx]

theorem add_one_le_iff [NoMaxOrder α] : x + 1 ≤ y ↔ x < y :=
  add_one_le_iff_of_not_isMax (not_isMax x)

@[simp]
theorem wcovBy_add_one (x : α) : x ⩿ x + 1 := by
  rw [← succ_eq_add_one]
  exact wcovBy_succ x

@[simp]
theorem covBy_add_one [NoMaxOrder α] (x : α) : x ⋖ x + 1 := by
  rw [← succ_eq_add_one]
  exact covBy_succ x

end Add

section Sub

variable [Sub α] [One α] [PredSubOrder α]

theorem pred_eq_sub_one (x : α) : pred x = x - 1 :=
  PredSubOrder.pred_eq_sub_one x

theorem le_sub_one_of_lt (h : x < y) : x ≤ y - 1 := by
  rw [← pred_eq_sub_one]
  exact le_pred_of_lt h

theorem le_sub_one_iff_of_not_isMin (hy : ¬ IsMin y) : x ≤ y - 1 ↔ x < y := by
  rw [← pred_eq_sub_one, le_pred_iff_of_not_isMin hy]

theorem le_sub_one_iff [NoMinOrder α] : x ≤ y - 1 ↔ x < y :=
  le_sub_one_iff_of_not_isMin (not_isMin y)

@[simp]
theorem sub_one_wcovBy (x : α) : x - 1 ⩿ x := by
  rw [← pred_eq_sub_one]
  exact pred_wcovBy x

@[simp]
theorem sub_one_covBy [NoMinOrder α] (x : α) : x - 1 ⋖ x := by
  rw [← pred_eq_sub_one]
  exact pred_covBy x

end Sub

@[simp]
theorem succ_iterate [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : ℕ) :
    succ^[n] x = x + n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, succ_eq_add_one, Nat.cast_one, add_assoc]

@[simp]
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
  rw [← succ_le_iff_of_not_isMax not_isMax_zero, succ_eq_add_one, zero_add]

theorem covBy_iff_add_one_eq [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    x ⋖ y ↔ x + 1 = y := by
  rw [← succ_eq_add_one]
  exact succ_eq_iff_covBy.symm

theorem covBy_iff_sub_one_eq [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] :
    x ⋖ y ↔ y - 1 = x := by
  rw [← pred_eq_sub_one]
  exact pred_eq_iff_covBy.symm

end PartialOrder

section LinearOrder

variable [LinearOrder α]

section Add

variable [Add α] [One α] [SuccAddOrder α]

theorem le_of_lt_add_one (h : x < y + 1) : x ≤ y := by
  rw [← succ_eq_add_one] at h
  exact le_of_lt_succ h

theorem lt_add_one_iff_of_not_isMax (hy : ¬ IsMax y) : x < y + 1 ↔ x ≤ y := by
  rw [← succ_eq_add_one, lt_succ_iff_of_not_isMax hy]

theorem lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x ≤ y :=
  lt_add_one_iff_of_not_isMax (not_isMax y)

end Add

section Sub

variable [Sub α] [One α] [PredSubOrder α]

theorem le_of_sub_one_lt (h : x - 1 < y) : x ≤ y := by
  rw [← pred_eq_sub_one] at h
  exact le_of_pred_lt h

theorem sub_one_lt_iff_of_not_isMin (hx : ¬ IsMin x) : x - 1 < y ↔ x ≤ y := by
  rw [← pred_eq_sub_one, pred_lt_iff_of_not_isMin hx]

theorem sub_one_lt_iff [NoMinOrder α] : x - 1 < y ↔ x ≤ y :=
  sub_one_lt_iff_of_not_isMin (not_isMin x)

end Sub

theorem lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : x < 1 ↔ x ≤ 0 := by
  rw [← lt_succ_iff_of_not_isMax not_isMax_zero, succ_eq_add_one, zero_add]

end LinearOrder

end Order
