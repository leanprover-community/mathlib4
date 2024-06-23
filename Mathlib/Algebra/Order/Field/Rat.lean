/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.NNRat.Defs

#align_import data.rat.basic from "leanprover-community/mathlib"@"a59dad53320b73ef180174aae867addd707ef00e"

/-!
# The rational numbers form a linear ordered field

This file contains the linear ordered field instance on the rational numbers.

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

namespace Rat

instance instLinearOrderedField : LinearOrderedField ℚ where
  __ := instLinearOrderedCommRing
  __ := instField

end Rat

-- The `LinearOrderedSemifield` and `LinearOrderedCommGroupWithZero` instances are shortcut
-- instances for performance
deriving instance CanonicallyLinearOrderedSemifield, LinearOrderedSemifield,
  LinearOrderedCommGroupWithZero for NNRat

/-! ### Miscellaneous lemmas -/

namespace NNRat

@[simp, norm_cast] lemma coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = (q : ℚ)⁻¹ := rfl
#align nnrat.coe_inv NNRat.coe_inv
@[simp, norm_cast] lemma coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q := rfl
#align nnrat.coe_div NNRat.coe_div

lemma inv_def (q : ℚ≥0) : q⁻¹ = divNat q.den q.num := by ext; simp [Rat.inv_def', num_coe, den_coe]
lemma div_def (p q : ℚ≥0) : p / q = divNat (p.num * q.den) (p.den * q.num) := by
  ext; simp [Rat.div_def', num_coe, den_coe]

lemma num_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.num = q.den := by
  rw [inv_def, divNat, num, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq),
    Int.natAbs_ofNat]
  simpa using q.coprime_num_den.symm

lemma den_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.den = q.num := by
  rw [inv_def, divNat, den, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]
  simpa using q.coprime_num_den.symm

end NNRat
