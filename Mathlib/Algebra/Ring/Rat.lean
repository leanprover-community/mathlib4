/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Int
import Mathlib.Data.Rat.Defs

#align_import data.rat.defs from "leanprover-community/mathlib"@"18a5306c091183ac90884daa9373fa3b178e8607"

/-!
# The rational numbers are a commutative ring

This file contains the commutative ring instance on the rational numbers.

See note [foundational algebra order theory].
-/

assert_not_exists OrderedCommMonoid
assert_not_exists Field
assert_not_exists PNat
assert_not_exists Nat.dvd_mul
assert_not_exists IsDomain.toCancelMonoidWithZero

namespace Rat

/-! ### Instances -/

instance commRing : CommRing ℚ where
  __ := addCommGroup
  __ := commMonoid
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  intCast := fun n => n
  natCast n := Int.cast n
  natCast_zero := rfl
  natCast_succ n := by
    simp only [intCast_eq_divInt, divInt_add_divInt _ _ Int.one_ne_zero Int.one_ne_zero,
      ← divInt_one_one, Int.natCast_add, Int.natCast_one, mul_one]

instance commGroupWithZero : CommGroupWithZero ℚ :=
  { exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
    inv_zero := by
      change Rat.inv 0 = 0
      rw [Rat.inv_def]
      rfl
    mul_inv_cancel := Rat.mul_inv_cancel
    mul_zero := mul_zero
    zero_mul := zero_mul }

instance isDomain : IsDomain ℚ := NoZeroDivisors.to_isDomain _
instance instCharZero : CharZero ℚ where cast_injective a b hab := by simpa using congr_arg num hab

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance commSemiring : CommSemiring ℚ := by infer_instance
instance semiring     : Semiring ℚ     := by infer_instance

/-! ### Miscellaneous lemmas -/

lemma mkRat_eq_div (n : ℤ) (d : ℕ) : mkRat n d = n / d := by
  simp only [mkRat_eq_divInt, divInt_eq_div, Int.cast_natCast]

lemma divInt_div_divInt_cancel_left {x : ℤ} (hx : x ≠ 0) (n d : ℤ) :
    n /. x / (d /. x) = n /. d := by
  rw [div_eq_mul_inv, inv_divInt', divInt_mul_divInt_cancel hx]
#align rat.mk_div_mk_cancel_left Rat.divInt_div_divInt_cancel_left

lemma divInt_div_divInt_cancel_right {x : ℤ} (hx : x ≠ 0) (n d : ℤ) :
    x /. n / (x /. d) = d /. n := by
  rw [div_eq_mul_inv, inv_divInt', mul_comm, divInt_mul_divInt_cancel hx]
#align rat.mk_div_mk_cancel_right Rat.divInt_div_divInt_cancel_right

lemma num_div_den (r : ℚ) : (r.num : ℚ) / (r.den : ℚ) = r := by
  rw [← Int.cast_natCast, ← divInt_eq_div, num_divInt_den]
#align rat.num_div_denom Rat.num_div_den

@[simp] lemma divInt_pow (num : ℕ) (den : ℤ) (n : ℕ) : (num /. den) ^ n = num ^ n /. den ^ n := by
  simp [divInt_eq_div, div_pow, Int.natCast_pow]

@[simp] lemma mkRat_pow (num den : ℕ) (n : ℕ) : mkRat num den ^ n = mkRat (num ^ n) (den ^ n) := by
  rw [mkRat_eq_divInt, mkRat_eq_divInt, divInt_pow, Int.natCast_pow]

lemma natCast_eq_divInt (n : ℕ) : ↑n = n /. 1 := by rw [← Int.cast_natCast, intCast_eq_divInt]
#align rat.coe_nat_eq_mk Rat.natCast_eq_divInt

@[simp] lemma mul_den_eq_num (q : ℚ) : q * q.den = q.num := by
  suffices (q.num /. ↑q.den) * (↑q.den /. 1) = q.num /. 1 by
    conv => pattern (occs := 1) q; (rw [← num_divInt_den q])
    simp only [intCast_eq_divInt, natCast_eq_divInt, num_divInt_den] at this ⊢; assumption
  have : (q.den : ℤ) ≠ 0 := mod_cast q.den_ne_zero
  rw [divInt_mul_divInt _ _ this Int.one_ne_zero, mul_comm (q.den : ℤ) 1, divInt_mul_right this]
#align rat.mul_denom_eq_num Rat.mul_den_eq_num

@[simp] lemma den_mul_eq_num (q : ℚ) : q.den * q = q.num := by rw [mul_comm, mul_den_eq_num]

@[deprecated (since := "2024-04-07")] alias coe_nat_eq_divInt := natCast_eq_divInt

end Rat
