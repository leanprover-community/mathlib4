/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Tactic.FinCases

/-!
# The order on `Fin n` is succ-archimedean

We relate `Order.succ` and `Fin.succ` and show that `Fin n` is succ-archimedean.

-/

namespace Fin

lemma orderSucc_castSucc {n : ℕ} (i : Fin n) :
    Order.succ i.castSucc = i.succ := by
  dsimp [Order.succ]
  rw [if_pos (i.castSucc_lt_last)]
  aesop

lemma Order.succ_iterate_coe {n : ℕ} (i : Fin n) (k : ℕ) (hik : i + k < n) :
    Order.succ^[k] i = ⟨i + k, hik⟩ := by
  induction k generalizing i with
  | zero => simp
  | succ k hk =>
    rw [Function.iterate_succ, Function.comp_apply]
    obtain _ | n := n
    · fin_cases i
    · obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · dsimp at hik
        rw [orderSucc_castSucc, hk _ (by dsimp; omega)]
        ext
        dsimp
        omega
      · simp at hik

instance (n : ℕ) : IsSuccArchimedean (Fin n) where
  exists_succ_iterate_of_le := by
    rintro ⟨a, _⟩ ⟨b, hb⟩ (h : a ≤ b)
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact ⟨k, Order.succ_iterate_coe _ _ hb⟩

end Fin
