/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.SuccPred.Basic

/-!
# Successors and predecessors of `Fin n`

In this file, we show that `Fin n` is both a `SuccOrder` and a `PredOrder`. Note that they are
also archimedean, but this is derived from the general instance for well-orderings as opposed
to a specific `Fin` instance.

-/


namespace Fin

instance : ∀ {n : ℕ}, SuccOrder (Fin n)
  | 0 => by constructor <;> intro a <;> exact elim0 a
  | n + 1 =>
    SuccOrder.ofCore
      (fun i ↦ if hi : i = Fin.last n
        then Fin.last n else i.succ.castPred (by simpa [← Fin.succ_last]))
      (fun {i} hi j ↦ by
        dsimp
        rw [dif_neg (by simpa using hi)]
        rfl)
      (fun i hi ↦ by
        obtain rfl : i = Fin.last _ := by simpa using hi
        simp)

@[simp]
lemma orderSucc_last (n : ℕ)  :
    Order.succ (Fin.last n) = Fin.last n :=
  dif_pos rfl

@[simp]
lemma orderSucc_castSucc {n : ℕ} (i : Fin n) :
    Order.succ i.castSucc = i.succ :=
  dif_neg (fun h ↦ by
    simp only [Fin.ext_iff, coe_castSucc, val_last] at h
    omega)

theorem succ_eq {n : ℕ} :
    Order.succ = fun a : Fin (n + 1) => if a < Fin.last n then a + 1 else a := by
  ext a : 1
  obtain ⟨a, rfl⟩ | rfl := a.eq_castSucc_or_eq_last
  · simp [if_pos a.castSucc_lt_last]
  · simp

theorem succ_apply {n : ℕ} (a : Fin (n + 1)) :
    Order.succ a = if a < Fin.last n then a + 1 else a := by
  rw [succ_eq]

instance : ∀ {n : ℕ}, PredOrder (Fin n)
  | 0 => by constructor <;> first | intro a; exact elim0 a
  | n + 1 =>
    PredOrder.ofCore
      (fun i ↦ if hi : i = 0 then 0 else (i.pred hi).castSucc)
      (fun {i} hi j ↦ by
        dsimp
        rw [dif_neg (by simpa using hi), Fin.le_castSucc_pred_iff])
      (fun i hi ↦ by
        obtain rfl : i = 0 := by simpa using hi
        simp)

@[simp]
lemma orderPred_zero (n : ℕ) :
    Order.pred (0 : Fin (n + 1)) = 0 :=
  rfl

@[simp]
lemma orderPred_succ {n : ℕ} (i : Fin n) :
    Order.pred i.succ = i.castSucc :=
  rfl

theorem pred_eq {n} : Order.pred = fun a : Fin (n + 1) => if a = 0 then 0 else a - 1 := by
  ext a : 1
  obtain rfl | ⟨a, rfl⟩ := a.eq_zero_or_eq_succ
  · rfl
  · rw [orderPred_succ, if_neg a.succ_ne_zero, ← add_left_inj 1,
      coeSucc_eq_succ, sub_add_cancel]

theorem pred_apply {n : ℕ} (a : Fin (n + 1)) : Order.pred a = if a = 0 then 0 else a - 1 := by
  rw [pred_eq]

attribute [deprecated "Use orderSucc_castSucc or orderSucc_last" (since := "2025-02-05")]
  succ_eq succ_apply

attribute [deprecated "Use orderPred_zero or orderPred_succ" (since := "2025-02-05")]
  pred_eq pred_apply

end Fin
