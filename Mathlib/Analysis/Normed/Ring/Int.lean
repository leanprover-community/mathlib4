/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `‖n‖` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `NNReal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `‖n‖₊`.
-/

public section


namespace Int

theorem nnNorm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖₊ = 1 := by
  obtain rfl | rfl := units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnNorm_neg, nnNorm_one]

@[deprecated (since := "2026-10-31")] alias nnnorm_coe_units := nnNorm_coe_units

theorem norm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖ = 1 := by
  rw [← coe_nnNorm, nnNorm_coe_units, NNReal.coe_one]

@[simp]
theorem nnNorm_natCast (n : ℕ) : ‖(n : ℤ)‖₊ = n :=
  Real.nnNorm_natCast _

@[deprecated (since := "2026-10-31")] alias nnnorm_natCast := nnNorm_natCast

@[simp] lemma enorm_natCast (n : ℕ) : ‖(n : ℤ)‖ₑ = n := Real.enorm_natCast _

@[simp]
theorem toNat_add_toNat_neg_eq_nnNorm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊ := by
  rw [← Nat.cast_add, toNat_add_toNat_neg_eq_natAbs, NNReal.natCast_natAbs]

@[deprecated (since := "2026-10-31")]
alias toNat_add_toNat_neg_eq_nnnorm := toNat_add_toNat_neg_eq_nnNorm

@[simp]
theorem toNat_add_toNat_neg_eq_norm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖ := by
  simpa only [NNReal.coe_natCast, NNReal.coe_add] using!
    congrArg NNReal.toReal (toNat_add_toNat_neg_eq_nnNorm n)

end Int
