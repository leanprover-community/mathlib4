/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module data.fin.succ_pred
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Order.SuccPred.Basic

/-!
# Successors and predecessors of `fin n`

In this file, we show that `fin n` is both a `succ_order` and a `pred_order`. Note that they are
also archimedean, but this is derived from the general instance for well-orderings as opposed
to a specific `fin` instance.

-/


namespace Fin

instance : ∀ {n : ℕ}, SuccOrder (Fin n)
  | 0 => by constructor <;> exact elim0
  | n + 1 =>
    SuccOrder.ofCore (fun i => if i < Fin.last n then i + 1 else i)
      (by
        intro a ha b
        rw [isMax_iff_eq_top, eq_top_iff, not_le, top_eq_last] at ha
        rw [if_pos ha, lt_iff_coe_lt_coe, le_iff_coe_le_coe, coe_add_one_of_lt ha]
        exact Nat.lt_iff_add_one_le)
      (by
        intro a ha
        rw [isMax_iff_eq_top, top_eq_last] at ha
        rw [if_neg ha.not_lt])

@[simp]
theorem succ_eq {n : ℕ} : SuccOrder.succ = fun a => if a < Fin.last n then a + 1 else a :=
  rfl
#align fin.succ_eq Fin.succ_eq

@[simp]
theorem succ_apply {n : ℕ} (a) : SuccOrder.succ a = if a < Fin.last n then a + 1 else a :=
  rfl
#align fin.succ_apply Fin.succ_apply

instance : ∀ {n : ℕ}, PredOrder (Fin n)
  | 0 => by constructor <;> exact elim0
  | n + 1 =>
    PredOrder.ofCore (fun x => if x = 0 then 0 else x - 1)
      (by
        intro a ha b
        rw [isMin_iff_eq_bot, eq_bot_iff, not_le, bot_eq_zero] at ha
        rw [if_neg ha.ne', lt_iff_coe_lt_coe, le_iff_coe_le_coe, coe_sub_one, if_neg ha.ne',
          le_tsub_iff_right, Iff.comm]
        exact Nat.lt_iff_add_one_le
        exact ha)
      (by
        intro a ha
        rw [isMin_iff_eq_bot, bot_eq_zero] at ha
        rwa [if_pos ha, eq_comm])

@[simp]
theorem pred_eq {n} : PredOrder.pred = fun a : Fin (n + 1) => if a = 0 then 0 else a - 1 :=
  rfl
#align fin.pred_eq Fin.pred_eq

@[simp]
theorem pred_apply {n : ℕ} (a : Fin (n + 1)) : PredOrder.pred a = if a = 0 then 0 else a - 1 :=
  rfl
#align fin.pred_apply Fin.pred_apply

end Fin

