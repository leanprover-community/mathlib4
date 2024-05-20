/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fin.Basic
import Mathlib.Order.SuccPred.Basic

#align_import data.nat.succ_pred from "leanprover-community/mathlib"@"a2d2e18906e2b62627646b5d5be856e6a642062f"

/-!
# Successors and predecessors of naturals

In this file, we show that `ℕ` is both an archimedean `succOrder` and an archimedean `predOrder`.
-/


open Function Order

namespace Nat
variable {m n : ℕ}

-- so that Lean reads `Nat.succ` through `succ_order.succ`
@[instance] abbrev instSuccOrder  : SuccOrder ℕ :=
  SuccOrder.ofSuccLeIff succ Nat.succ_le

-- so that Lean reads `Nat.pred` through `pred_order.pred`
@[instance] abbrev instPredOrder : PredOrder ℕ where
  pred := pred
  pred_le := pred_le
  min_of_le_pred {a} ha := by
    cases a
    · exact isMin_bot
    · exact (not_succ_le_self _ ha).elim
  le_pred_of_lt {a} {b} h := by
    cases b
    · exact (a.not_lt_zero h).elim
    · exact le_of_succ_le_succ h
  le_of_pred_lt {a} {b} h := by
    cases a
    · exact b.zero_le
    · exact h

@[simp]
theorem succ_eq_succ : Order.succ = succ :=
  rfl
#align nat.succ_eq_succ Nat.succ_eq_succ

@[simp]
theorem pred_eq_pred : Order.pred = pred :=
  rfl
#align nat.pred_eq_pred Nat.pred_eq_pred

theorem succ_iterate (a : ℕ) : ∀ n, succ^[n] a = a + n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ', add_succ]
    exact congr_arg _ (succ_iterate a n)
#align nat.succ_iterate Nat.succ_iterate

theorem pred_iterate (a : ℕ) : ∀ n, pred^[n] a = a - n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ', sub_succ]
    exact congr_arg _ (pred_iterate a n)
#align nat.pred_iterate Nat.pred_iterate

lemma le_succ_iff_eq_or_le : m ≤ n.succ ↔ m = n.succ ∨ m ≤ n := Order.le_succ_iff_eq_or_le

instance : IsSuccArchimedean ℕ :=
  ⟨fun {a} {b} h => ⟨b - a, by rw [succ_eq_succ, succ_iterate, add_tsub_cancel_of_le h]⟩⟩

instance : IsPredArchimedean ℕ :=
  ⟨fun {a} {b} h => ⟨b - a, by rw [pred_eq_pred, pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩

lemma forall_ne_zero_iff (P : ℕ → Prop) :
    (∀ i, i ≠ 0 → P i) ↔ (∀ i, P (i + 1)) :=
  SuccOrder.forall_ne_bot_iff P

/-! ### Covering relation -/


protected theorem covBy_iff_succ_eq {m n : ℕ} : m ⋖ n ↔ m + 1 = n :=
  succ_eq_iff_covBy.symm
#align nat.covby_iff_succ_eq Nat.covBy_iff_succ_eq

end Nat

@[simp, norm_cast]
theorem Fin.coe_covBy_iff {n : ℕ} {a b : Fin n} : (a : ℕ) ⋖ b ↔ a ⋖ b :=
  and_congr_right' ⟨fun h _c hc => h hc, fun h c ha hb => @h ⟨c, hb.trans b.prop⟩ ha hb⟩
#align fin.coe_covby_iff Fin.coe_covBy_iff

alias ⟨_, CovBy.coe_fin⟩ := Fin.coe_covBy_iff
#align covby.coe_fin CovBy.coe_fin
