/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.NNRat.Defs

/-!
# The rational numbers form a field

This file contains the field instance on the rational numbers.

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

namespace Rat

instance instField : Field ℚ where
  __ := commRing
  __ := commGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← NNRat.den_coe, ← Int.cast_natCast q.num, ← NNRat.num_coe]; exact(num_div_den _).symm
  ratCast_def _ := (num_div_den _).symm

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instDivisionRing : DivisionRing ℚ := inferInstance

protected lemma inv_nonneg {a : ℚ} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by
  rw [inv_def']
  exact divInt_nonneg (Int.natCast_nonneg a.den) (num_nonneg.mpr ha)

protected lemma div_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  mul_nonneg ha (Rat.inv_nonneg hb)

protected lemma zpow_nonneg {a : ℚ} (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | Int.ofNat n => by simp [ha]
  | Int.negSucc n => by simpa using Rat.inv_nonneg (pow_nonneg ha (n + 1))

end Rat

namespace NNRat

instance instInv : Inv ℚ≥0 where
  inv x := ⟨x⁻¹, Rat.inv_nonneg x.2⟩

instance instDiv : Div ℚ≥0 where
  div x y := ⟨x / y, Rat.div_nonneg x.2 y.2⟩

instance instZPow : Pow ℚ≥0 ℤ where
  pow x n := ⟨x ^ n, Rat.zpow_nonneg x.2 n⟩

@[simp, norm_cast] lemma coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = (q : ℚ)⁻¹ := rfl
@[simp, norm_cast] lemma coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q := rfl
@[simp, norm_cast] lemma coe_zpow (p : ℚ≥0) (n : ℤ) : ((p ^ n : ℚ≥0) : ℚ) = p ^ n := rfl

lemma inv_def (q : ℚ≥0) : q⁻¹ = divNat q.den q.num := by ext; simp [Rat.inv_def', num_coe, den_coe]
lemma div_def (p q : ℚ≥0) : p / q = divNat (p.num * q.den) (p.den * q.num) := by
  ext; simp [Rat.div_def', num_coe, den_coe]

lemma num_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.num = q.den := by
  rw [inv_def, divNat, num, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq),
    Int.natAbs_natCast]
  simpa using q.coprime_num_den.symm

lemma den_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.den = q.num := by
  rw [inv_def, divNat, den, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]
  simpa using q.coprime_num_den.symm

@[simp]
lemma num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q := by
  ext1
  rw [coe_div, coe_natCast, coe_natCast, num, ← Int.cast_natCast]
  exact (cast_def _).symm

instance instSemifield : Semifield ℚ≥0 where
  __ := instNNRatCommSemiring
  inv_zero := by ext; simp
  mul_inv_cancel q h := by ext; simp [h]
  nnratCast_def q := q.num_div_den.symm
  nnqsmul q a := q * a
  nnqsmul_def q a := rfl
  zpow n a := a ^ n
  zpow_zero' a := by ext; norm_cast
  zpow_succ' n a := by ext; norm_cast
  zpow_neg' n a := by ext; norm_cast

end NNRat
