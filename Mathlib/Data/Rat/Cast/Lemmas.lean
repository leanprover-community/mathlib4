/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Field.Basic

#align_import data.rat.cast from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"


/-!
# Some exiled lemmas about casting

These lemmas have been removed from `Mathlib.Data.Rat.Cast.Defs`
to avoiding needing to import `Mathlib.Algebra.Field.Basic` there.

In fact, these lemmas don't appear to be used anywhere in Mathlib,
so perhaps this file can simply be deleted.
-/

namespace Rat

variable {α : Type*} [DivisionRing α]

-- Porting note: rewrote proof
@[simp]
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  cases' n with n
  · simp
  rw [cast_def, inv_coe_nat_num, inv_coe_nat_den, if_neg n.succ_ne_zero,
    Int.sign_eq_one_of_pos (Nat.cast_pos.mpr n.succ_pos), Int.cast_one, one_div]
#align rat.cast_inv_nat Rat.cast_inv_nat

-- Porting note: proof got a lot easier - is this still the intended statement?
@[simp]
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  cases' n with n n
  · simp [ofInt_eq_cast, cast_inv_nat]
  · simp only [ofInt_eq_cast, Int.cast_negSucc, ← Nat.cast_succ, cast_neg, inv_neg, cast_inv_nat]
#align rat.cast_inv_int Rat.cast_inv_int
