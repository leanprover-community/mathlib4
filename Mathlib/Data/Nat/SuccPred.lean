/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Fin.Basic
import Mathlib.Order.SuccPred.Archimedean

/-!
# Successors and predecessors of naturals

In this file, we show that `ℕ` is both an archimedean `succOrder` and an archimedean `predOrder`.
-/


open Function Order

namespace Nat
variable {m n : ℕ}

-- so that Lean reads `Nat.succ` through `succ_order.succ`
@[instance] abbrev instSuccOrder : SuccOrder ℕ :=
  SuccOrder.ofSuccLeIff succ Nat.succ_le

instance instSuccAddOrder : SuccAddOrder ℕ := ⟨fun _ => rfl⟩

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

instance instPredSubOrder : PredSubOrder ℕ := ⟨fun _ => rfl⟩

@[simp]
theorem succ_eq_succ : Order.succ = succ :=
  rfl

@[simp]
theorem pred_eq_pred : Order.pred = pred :=
  rfl

protected theorem succ_iterate (a : ℕ) : ∀ n, succ^[n] a = a + n :=
  Order.succ_iterate a

protected theorem pred_iterate (a : ℕ) : ∀ n, pred^[n] a = a - n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ', sub_succ]
    exact congr_arg _ (Nat.pred_iterate a n)

lemma le_succ_iff_eq_or_le : m ≤ n.succ ↔ m = n.succ ∨ m ≤ n := Order.le_succ_iff_eq_or_le

instance : IsSuccArchimedean ℕ :=
  ⟨fun {a} {b} h => ⟨b - a, by rw [succ_eq_succ, Nat.succ_iterate, add_tsub_cancel_of_le h]⟩⟩

instance : IsPredArchimedean ℕ :=
  ⟨fun {a} {b} h => ⟨b - a, by rw [pred_eq_pred, Nat.pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩

lemma forall_ne_zero_iff (P : ℕ → Prop) :
    (∀ i, i ≠ 0 → P i) ↔ (∀ i, P (i + 1)) :=
  SuccOrder.forall_ne_bot_iff P

/-! ### Covering relation -/


@[deprecated Order.covBy_iff_add_one_eq (since := "2024-09-04")]
protected theorem covBy_iff_succ_eq {m n : ℕ} : m ⋖ n ↔ m + 1 = n :=
  covBy_iff_add_one_eq

end Nat

@[simp, norm_cast]
theorem Fin.coe_covBy_iff {n : ℕ} {a b : Fin n} : (a : ℕ) ⋖ b ↔ a ⋖ b :=
  and_congr_right' ⟨fun h _c hc => h hc, fun h c ha hb => @h ⟨c, hb.trans b.prop⟩ ha hb⟩

alias ⟨_, CovBy.coe_fin⟩ := Fin.coe_covBy_iff
