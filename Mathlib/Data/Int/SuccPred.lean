/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.SuccPred

#align_import data.int.succ_pred from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Successors and predecessors of integers

In this file, we show that `ℤ` is both an archimedean `SuccOrder` and an archimedean `PredOrder`.
-/


open Function Order

namespace Int

-- so that Lean reads `Int.succ` through `SuccOrder.succ`
@[reducible]
instance : SuccOrder ℤ :=
  { SuccOrder.ofSuccLeIff succ fun {_ _} => Iff.rfl with succ := succ }

-- so that Lean reads `Int.pred` through `PredOrder.pred`
@[reducible]
instance : PredOrder ℤ where
  pred := pred
  pred_le _ := (sub_one_lt_of_le le_rfl).le
  min_of_le_pred ha := ((sub_one_lt_of_le le_rfl).not_le ha).elim
  le_pred_of_lt {_ _} := le_sub_one_of_lt
  le_of_pred_lt {_ _} := le_of_sub_one_lt

@[simp]
theorem succ_eq_succ : Order.succ = succ :=
  rfl
#align int.succ_eq_succ Int.succ_eq_succ

@[simp]
theorem pred_eq_pred : Order.pred = pred :=
  rfl
#align int.pred_eq_pred Int.pred_eq_pred

theorem pos_iff_one_le {a : ℤ} : 0 < a ↔ 1 ≤ a :=
  Order.succ_le_iff.symm
#align int.pos_iff_one_le Int.pos_iff_one_le

theorem succ_iterate (a : ℤ) : ∀ n, succ^[n] a = a + n
  | 0 => (add_zero a).symm
  | n + 1 => by
    rw [Function.iterate_succ', Int.ofNat_succ, ← add_assoc]
    exact congr_arg _ (succ_iterate a n)
#align int.succ_iterate Int.succ_iterate

theorem pred_iterate (a : ℤ) : ∀ n, pred^[n] a = a - n
  | 0 => (sub_zero a).symm
  | n + 1 => by
    rw [Function.iterate_succ', Int.ofNat_succ, ← sub_sub]
    exact congr_arg _ (pred_iterate a n)
#align int.pred_iterate Int.pred_iterate

instance : IsSuccArchimedean ℤ :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by
      rw [succ_eq_succ, succ_iterate, toNat_sub_of_le h, ← add_sub_assoc, add_sub_cancel']⟩⟩

instance : IsPredArchimedean ℤ :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [pred_eq_pred, pred_iterate, toNat_sub_of_le h, sub_sub_cancel]⟩⟩

/-! ### Covering relation -/


protected theorem covby_iff_succ_eq {m n : ℤ} : m ⋖ n ↔ m + 1 = n :=
  succ_eq_iff_covby.symm
#align int.covby_iff_succ_eq Int.covby_iff_succ_eq

@[simp]
theorem sub_one_covby (z : ℤ) : z - 1 ⋖ z := by rw [Int.covby_iff_succ_eq, sub_add_cancel]
#align int.sub_one_covby Int.sub_one_covby

@[simp]
theorem covby_add_one (z : ℤ) : z ⋖ z + 1 :=
  Int.covby_iff_succ_eq.mpr rfl
#align int.covby_add_one Int.covby_add_one

end Int

@[simp, norm_cast]
theorem Nat.cast_int_covby_iff {a b : ℕ} : (a : ℤ) ⋖ b ↔ a ⋖ b := by
  rw [Nat.covby_iff_succ_eq, Int.covby_iff_succ_eq]
  exact Int.coe_nat_inj'
#align nat.cast_int_covby_iff Nat.cast_int_covby_iff

alias ⟨_, Covby.cast_int⟩ := Nat.cast_int_covby_iff
#align covby.cast_int Covby.cast_int
