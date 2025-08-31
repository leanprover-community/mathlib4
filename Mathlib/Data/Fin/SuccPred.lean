/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
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
    SuccOrder.ofCore (Fin.lastCases (Fin.last n) Fin.succ)
      (fun {i} hi j ↦ by
        obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (by simpa using hi)
        simp [castSucc_lt_iff_succ_le])
      (fun i hi ↦ by
        obtain rfl : i = Fin.last n := by simpa using hi
        simp)

lemma orderSucc_eq {n : ℕ} :
    Order.succ = Fin.lastCases (Fin.last n) Fin.succ := rfl

lemma orderSucc_apply {n : ℕ} (i : Fin (n + 1)) :
    Order.succ i = Fin.lastCases (Fin.last n) Fin.succ i := rfl

@[simp]
lemma orderSucc_last (n : ℕ)  :
    Order.succ (Fin.last n) = Fin.last n := by
  simp [orderSucc_apply]

@[simp]
lemma orderSucc_castSucc {n : ℕ} (i : Fin n) :
    Order.succ i.castSucc = i.succ := by
  simp [orderSucc_apply]

@[deprecated (since := "2025-02-06")] alias succ_eq := orderSucc_eq
@[deprecated (since := "2025-02-06")] alias succ_apply := orderSucc_apply

instance : ∀ {n : ℕ}, PredOrder (Fin n)
  | 0 => by constructor <;> first | intro a; exact elim0 a
  | n + 1 =>
    PredOrder.ofCore
      (Fin.cases 0 Fin.castSucc)
      (fun {i} hi j ↦ by
        obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (by simpa using hi)
        simp [le_castSucc_iff])
      (fun i hi ↦ by
        obtain rfl : i = 0 := by simpa using hi
        rfl)

lemma orderPred_eq {n : ℕ} :
    Order.succ = Fin.lastCases (Fin.last n) Fin.succ := rfl

lemma orderPred_apply {n : ℕ} (i : Fin (n + 1)) :
    Order.pred i = Fin.cases 0 Fin.castSucc i := rfl

@[simp]
lemma orderPred_zero (n : ℕ) :
    Order.pred (0 : Fin (n + 1)) = 0 :=
  rfl

@[simp]
lemma orderPred_succ {n : ℕ} (i : Fin n) :
    Order.pred i.succ = i.castSucc :=
  rfl

@[deprecated (since := "2025-02-06")] alias pred_eq := orderPred_eq
@[deprecated (since := "2025-02-06")] alias pred_apply := orderPred_apply

end Fin
