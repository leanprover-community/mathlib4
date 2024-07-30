/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.SuccPred

/-!
# Successors and predecessors of integers

In this file, we show that `ℤ` is both an archimedean `SuccOrder` and an archimedean `PredOrder`.
-/


open Function Order

namespace Int

-- so that Lean reads `Int.succ` through `SuccOrder.succ`
@[instance] abbrev instSuccOrder : SuccOrder ℤ :=
  { SuccOrder.ofSuccLeIff succ fun {_ _} => Iff.rfl with succ := succ }

-- so that Lean reads `Int.pred` through `PredOrder.pred`
@[instance] abbrev instPredOrder : PredOrder ℤ where
  pred := pred
  pred_le _ := (sub_one_lt_of_le le_rfl).le
  min_of_le_pred ha := ((sub_one_lt_of_le le_rfl).not_le ha).elim
  le_pred_of_lt {_ _} := le_sub_one_of_lt
  le_of_pred_lt {_ _} := le_of_sub_one_lt

@[simp]
theorem succ_eq_succ : Order.succ = succ :=
  rfl

@[simp]
theorem pred_eq_pred : Order.pred = pred :=
  rfl

theorem pos_iff_one_le {a : ℤ} : 0 < a ↔ 1 ≤ a :=
  Order.succ_le_iff.symm

theorem succ_iterate (a : ℤ) : ∀ n, succ^[n] a = a + n
  | 0 => (add_zero a).symm
  | n + 1 => by
    rw [Function.iterate_succ', Int.ofNat_succ, ← add_assoc]
    exact congr_arg _ (succ_iterate a n)

theorem pred_iterate (a : ℤ) : ∀ n, pred^[n] a = a - n
  | 0 => (sub_zero a).symm
  | n + 1 => by
    rw [Function.iterate_succ', Int.ofNat_succ, ← sub_sub]
    exact congr_arg _ (pred_iterate a n)

instance : IsSuccArchimedean ℤ :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by
      rw [succ_eq_succ, succ_iterate, toNat_sub_of_le h, ← add_sub_assoc, add_sub_cancel_left]⟩⟩

instance : IsPredArchimedean ℤ :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [pred_eq_pred, pred_iterate, toNat_sub_of_le h, sub_sub_cancel]⟩⟩

/-! ### Covering relation -/


protected theorem covBy_iff_succ_eq {m n : ℤ} : m ⋖ n ↔ m + 1 = n :=
  succ_eq_iff_covBy.symm

@[simp]
theorem sub_one_covBy (z : ℤ) : z - 1 ⋖ z := by rw [Int.covBy_iff_succ_eq, sub_add_cancel]

@[simp]
theorem covBy_add_one (z : ℤ) : z ⋖ z + 1 :=
  Int.covBy_iff_succ_eq.mpr rfl

@[simp, norm_cast]
theorem natCast_covBy {a b : ℕ} : (a : ℤ) ⋖ b ↔ a ⋖ b := by
  rw [Nat.covBy_iff_succ_eq, Int.covBy_iff_succ_eq]
  exact Int.natCast_inj

end Int

alias ⟨_, CovBy.intCast⟩ := Int.natCast_covBy

@[deprecated (since := "2024-05-27")] alias Nat.cast_int_covBy_iff := Int.natCast_covBy
@[deprecated (since := "2024-05-27")] alias CovBy.cast_int := CovBy.intCast
