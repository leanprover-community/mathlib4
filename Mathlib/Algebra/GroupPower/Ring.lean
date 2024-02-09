/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.GroupPower.Hom
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Nat.Order.Basic

#align_import algebra.group_power.ring from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Power operations on monoids with zero, semirings, and rings

This file provides additional lemmas about the natural power operator on rings and semirings.
Further lemmas about ordered semirings and rings can be found in `Algebra.GroupPower.Order`.
-/

variable {R S M : Type*}

section MonoidWithZero

variable [MonoidWithZero M]

theorem Ring.inverse_pow (r : M) : ∀ n : ℕ, Ring.inverse r ^ n = Ring.inverse (r ^ n)
  | 0 => by rw [pow_zero, pow_zero, Ring.inverse_one]
  | n + 1 => by
    rw [pow_succ, pow_succ', Ring.mul_inverse_rev' ((Commute.refl r).pow_left n),
      Ring.inverse_pow r n]
#align ring.inverse_pow Ring.inverse_pow

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero M] {n : ℕ} (hn : n ≠ 0)

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `MonoidWithZeroHom` -/
def powMonoidWithZeroHom : M →*₀ M :=
  { powMonoidHom n with map_zero' := zero_pow hn }
#align pow_monoid_with_zero_hom powMonoidWithZeroHom

@[simp]
theorem coe_powMonoidWithZeroHom : (powMonoidWithZeroHom hn : M → M) = fun x ↦ (x^n : M) := rfl
#align coe_pow_monoid_with_zero_hom coe_powMonoidWithZeroHom

@[simp]
theorem powMonoidWithZeroHom_apply (a : M) : powMonoidWithZeroHom hn a = a ^ n :=
  rfl
#align pow_monoid_with_zero_hom_apply powMonoidWithZeroHom_apply

end CommMonoidWithZero

theorem pow_dvd_pow_iff [CancelCommMonoidWithZero R] {x : R} {n m : ℕ} (h0 : x ≠ 0)
    (h1 : ¬IsUnit x) : x ^ n ∣ x ^ m ↔ n ≤ m := by
  constructor
  · intro h
    rw [← not_lt]
    intro hmn
    apply h1
    have : x ^ m * x ∣ x ^ m * 1 := by
      rw [← pow_succ', mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    apply pow_ne_zero m h0
  · apply pow_dvd_pow
#align pow_dvd_pow_iff pow_dvd_pow_iff

section Semiring

variable [Semiring R] [Semiring S]

protected theorem RingHom.map_pow (f : R →+* S) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a
#align ring_hom.map_pow RingHom.map_pow

theorem min_pow_dvd_add {n m : ℕ} {a b c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) :
    c ^ min n m ∣ a + b := by
  replace ha := (pow_dvd_pow c (min_le_left n m)).trans ha
  replace hb := (pow_dvd_pow c (min_le_right n m)).trans hb
  exact dvd_add ha hb
#align min_pow_dvd_add min_pow_dvd_add

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem add_sq (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [sq, add_mul_self_eq]
#align add_sq add_sq

theorem add_sq' (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [add_sq, add_assoc, add_comm _ (b ^ 2), add_assoc]
#align add_sq' add_sq'

alias add_pow_two := add_sq
#align add_pow_two add_pow_two

end CommSemiring

section HasDistribNeg

variable [Monoid R] [HasDistribNeg R]

variable (R)

theorem neg_one_pow_eq_or : ∀ n : ℕ, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1
  | 0 => Or.inl (pow_zero _)
  | n + 1 => (neg_one_pow_eq_or n).symm.imp
    (fun h ↦ by rw [pow_succ, h, neg_one_mul, neg_neg])
    (fun h ↦ by rw [pow_succ, h, mul_one])
#align neg_one_pow_eq_or neg_one_pow_eq_or

variable {R}

theorem neg_pow (a : R) (n : ℕ) : (-a) ^ n = (-1) ^ n * a ^ n :=
  neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n
#align neg_pow neg_pow

theorem neg_pow' (a : R) (n : ℕ) : (-a) ^ n = a ^ n * (-1) ^ n :=
  mul_neg_one a ▸ (Commute.neg_one_right a).mul_pow n

section
set_option linter.deprecated false

theorem neg_pow_bit0 (a : R) (n : ℕ) : (-a) ^ bit0 n = a ^ bit0 n := by
  rw [pow_bit0', neg_mul_neg, pow_bit0']
#align neg_pow_bit0 neg_pow_bit0

@[simp]
theorem neg_pow_bit1 (a : R) (n : ℕ) : (-a) ^ bit1 n = -a ^ bit1 n := by
  simp only [bit1, pow_succ, neg_pow_bit0, neg_mul_eq_neg_mul]
#align neg_pow_bit1 neg_pow_bit1

end

theorem neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]
#align neg_sq neg_sq

-- Porting note: removed the simp attribute to please the simpNF linter
theorem neg_one_sq : (-1 : R) ^ 2 = 1 := by simp [neg_sq, one_pow]
#align neg_one_sq neg_one_sq

alias neg_pow_two := neg_sq
#align neg_pow_two neg_pow_two

alias neg_one_pow_two := neg_one_sq
#align neg_one_pow_two neg_one_pow_two

end HasDistribNeg

section DivisionMonoid
variable [DivisionMonoid R] [HasDistribNeg R]

set_option linter.deprecated false in
@[simp] lemma zpow_bit0_neg (a : R) (n : ℤ) : (-a) ^ bit0 n = a ^ bit0 n := by
  rw [zpow_bit0', zpow_bit0', neg_mul_neg]
#align zpow_bit0_neg zpow_bit0_neg

end DivisionMonoid

section Ring

variable [Ring R] {a b : R}

protected theorem Commute.sq_sub_sq (h : Commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, h.mul_self_sub_mul_self_eq]
#align commute.sq_sub_sq Commute.sq_sub_sq

@[simp]
theorem neg_one_pow_mul_eq_zero_iff {n : ℕ} {r : R} : (-1) ^ n * r = 0 ↔ r = 0 := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]
#align neg_one_pow_mul_eq_zero_iff neg_one_pow_mul_eq_zero_iff

@[simp]
theorem mul_neg_one_pow_eq_zero_iff {n : ℕ} {r : R} : r * (-1) ^ n = 0 ↔ r = 0 := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]
#align mul_neg_one_pow_eq_zero_iff mul_neg_one_pow_eq_zero_iff

variable [NoZeroDivisors R]

protected theorem Commute.sq_eq_sq_iff_eq_or_eq_neg (h : Commute a b) :
    a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm]
#align commute.sq_eq_sq_iff_eq_or_eq_neg Commute.sq_eq_sq_iff_eq_or_eq_neg

@[simp]
theorem sq_eq_one_iff : a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg, one_pow]
#align sq_eq_one_iff sq_eq_one_iff

theorem sq_ne_one_iff : a ^ 2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 :=
  sq_eq_one_iff.not.trans not_or
#align sq_ne_one_iff sq_ne_one_iff

lemma neg_one_pow_eq_pow_mod_two (n : ℕ) : (-1 : R) ^ n = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2, pow_add, pow_mul]; simp [sq]
#align neg_one_pow_eq_pow_mod_two neg_one_pow_eq_pow_mod_two

end Ring

section CommRing

variable [CommRing R]

theorem sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
  (Commute.all a b).sq_sub_sq
#align sq_sub_sq sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq
#align pow_two_sub_pow_two pow_two_sub_pow_two

theorem sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg]
#align sub_sq sub_sq

alias sub_pow_two := sub_sq
#align sub_pow_two sub_pow_two

theorem sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]
#align sub_sq' sub_sq'

variable [NoZeroDivisors R] {a b : R}

theorem sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
  (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg
#align sq_eq_sq_iff_eq_or_eq_neg sq_eq_sq_iff_eq_or_eq_neg

theorem eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 → a = b ∨ a = -b :=
  sq_eq_sq_iff_eq_or_eq_neg.1
#align eq_or_eq_neg_of_sq_eq_sq eq_or_eq_neg_of_sq_eq_sq

-- Copies of the above CommRing lemmas for `Units R`.
namespace Units

protected theorem sq_eq_sq_iff_eq_or_eq_neg {a b : Rˣ} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  simp_rw [ext_iff, val_pow_eq_pow_val, sq_eq_sq_iff_eq_or_eq_neg, Units.val_neg]
#align units.sq_eq_sq_iff_eq_or_eq_neg Units.sq_eq_sq_iff_eq_or_eq_neg

protected theorem eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
  Units.sq_eq_sq_iff_eq_or_eq_neg.1 h
#align units.eq_or_eq_neg_of_sq_eq_sq Units.eq_or_eq_neg_of_sq_eq_sq

end Units

end CommRing
