/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Analysis.Normed.Field.Basic

#align_import analysis.normed_space.int from "leanprover-community/mathlib"@"5cc2dfdd3e92f340411acea4427d701dc7ed26f8"

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `‖n‖` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `NNReal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `‖n‖₊`.
-/


open BigOperators

namespace Int

theorem nnnorm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖₊ = 1 := by
  obtain rfl | rfl := units_eq_one_or e <;>
  -- ⊢ ‖↑1‖₊ = 1
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]
    -- 🎉 no goals
    -- 🎉 no goals
#align int.nnnorm_coe_units Int.nnnorm_coe_units

theorem norm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖ = 1 := by
  rw [← coe_nnnorm, nnnorm_coe_units, NNReal.coe_one]
  -- 🎉 no goals
#align int.norm_coe_units Int.norm_coe_units

@[simp]
theorem nnnorm_coe_nat (n : ℕ) : ‖(n : ℤ)‖₊ = n :=
  Real.nnnorm_coe_nat _
#align int.nnnorm_coe_nat Int.nnnorm_coe_nat

@[simp]
theorem toNat_add_toNat_neg_eq_nnnorm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊ := by
  rw [← Nat.cast_add, toNat_add_toNat_neg_eq_natAbs, NNReal.coe_natAbs]
  -- 🎉 no goals
#align int.to_nat_add_to_nat_neg_eq_nnnorm Int.toNat_add_toNat_neg_eq_nnnorm

@[simp]
theorem toNat_add_toNat_neg_eq_norm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖ := by
  simpa only [NNReal.coe_nat_cast, NNReal.coe_add] using
    congrArg NNReal.toReal (toNat_add_toNat_neg_eq_nnnorm n)
#align int.to_nat_add_to_nat_neg_eq_norm Int.toNat_add_toNat_neg_eq_norm

end Int
