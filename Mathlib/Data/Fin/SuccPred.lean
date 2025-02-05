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

end Fin
