/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/

import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Hom.Ring
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Divisibility
import Mathlib.Data.Nat.Order.Basic

#align_import algebra.group_power.ring from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Power operations on monoids with zero, semirings, and rings

This file provides additional lemmas about the natural power operator on rings and semirings.
Further lemmas about ordered semirings and rings can be found in `Algebra.GroupPower.Lemmas`.

-/

variable {R S M : Type*}

section MonoidWithZero

variable [MonoidWithZero M]

theorem zero_pow : ∀ {n : ℕ}, 0 < n → (0 : M) ^ n = 0
  | n + 1, _ => by rw [pow_succ, zero_mul]
                   -- 🎉 no goals
#align zero_pow zero_pow

@[simp]
theorem zero_pow' : ∀ n : ℕ, n ≠ 0 → (0 : M) ^ n = 0
  | 0, h => absurd rfl h
  | k + 1, _ => by
    rw [pow_succ]
    -- ⊢ 0 * 0 ^ k = 0
    exact zero_mul _
    -- 🎉 no goals
#align zero_pow' zero_pow'

theorem zero_pow_eq (n : ℕ) : (0 : M) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  -- ⊢ 0 ^ n = 1
  · rw [h, pow_zero]
    -- 🎉 no goals
  · rw [zero_pow (Nat.pos_of_ne_zero h)]
    -- 🎉 no goals
#align zero_pow_eq zero_pow_eq

theorem pow_eq_zero_of_le {x : M} {n m : ℕ} (hn : n ≤ m) (hx : x ^ n = 0) : x ^ m = 0 := by
  rw [← tsub_add_cancel_of_le hn, pow_add, hx, mul_zero]
  -- 🎉 no goals
#align pow_eq_zero_of_le pow_eq_zero_of_le

theorem pow_eq_zero [NoZeroDivisors M] {x : M} {n : ℕ} (H : x ^ n = 0) : x = 0 := by
  induction' n with n ih
  -- ⊢ x = 0
  · rw [pow_zero] at H
    -- ⊢ x = 0
    rw [← mul_one x, H, mul_zero]
    -- 🎉 no goals
  · rw [pow_succ] at H
    -- ⊢ x = 0
    exact Or.casesOn (mul_eq_zero.1 H) id ih
    -- 🎉 no goals
#align pow_eq_zero pow_eq_zero

@[simp]
theorem pow_eq_zero_iff [NoZeroDivisors M] {a : M} {n : ℕ} (hn : 0 < n) : a ^ n = 0 ↔ a = 0 := by
  refine' ⟨pow_eq_zero, _⟩
  -- ⊢ a = 0 → a ^ n = 0
  rintro rfl
  -- ⊢ 0 ^ n = 0
  exact zero_pow hn
  -- 🎉 no goals
#align pow_eq_zero_iff pow_eq_zero_iff

theorem pow_eq_zero_iff' [NoZeroDivisors M] [Nontrivial M] {a : M} {n : ℕ} :
    a ^ n = 0 ↔ a = 0 ∧ n ≠ 0 := by cases (zero_le n).eq_or_gt <;> simp [*, ne_of_gt]
                                    -- ⊢ a ^ n = 0 ↔ a = 0 ∧ n ≠ 0
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align pow_eq_zero_iff' pow_eq_zero_iff'

theorem pow_ne_zero_iff [NoZeroDivisors M] {a : M} {n : ℕ} (hn : 0 < n) : a ^ n ≠ 0 ↔ a ≠ 0 :=
  (pow_eq_zero_iff hn).not
#align pow_ne_zero_iff pow_ne_zero_iff

theorem ne_zero_pow {a : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≠ 0 → a ≠ 0 := by
  contrapose!
  -- ⊢ a = 0 → a ^ n = 0
  rintro rfl
  -- ⊢ 0 ^ n = 0
  exact zero_pow' n hn
  -- 🎉 no goals
#align ne_zero_pow ne_zero_pow

@[field_simps]
theorem pow_ne_zero [NoZeroDivisors M] {a : M} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
  mt pow_eq_zero h
#align pow_ne_zero pow_ne_zero

instance NeZero.pow [NoZeroDivisors M] {x : M} [NeZero x] {n : ℕ} : NeZero (x ^ n) :=
  ⟨pow_ne_zero n NeZero.out⟩
#align ne_zero.pow NeZero.pow

theorem sq_eq_zero_iff [NoZeroDivisors M] {a : M} : a ^ 2 = 0 ↔ a = 0 :=
  pow_eq_zero_iff two_pos
#align sq_eq_zero_iff sq_eq_zero_iff

@[simp]
theorem zero_pow_eq_zero [Nontrivial M] {n : ℕ} : (0 : M) ^ n = 0 ↔ 0 < n := by
  constructor <;> intro h
  -- ⊢ 0 ^ n = 0 → 0 < n
                  -- ⊢ 0 < n
                  -- ⊢ 0 ^ n = 0
  · rw [pos_iff_ne_zero]
    -- ⊢ n ≠ 0
    rintro rfl
    -- ⊢ False
    simp at h
    -- 🎉 no goals
  · exact zero_pow' n h.ne.symm
    -- 🎉 no goals
#align zero_pow_eq_zero zero_pow_eq_zero

theorem Ring.inverse_pow (r : M) : ∀ n : ℕ, Ring.inverse r ^ n = Ring.inverse (r ^ n)
  | 0 => by rw [pow_zero, pow_zero, Ring.inverse_one]
            -- 🎉 no goals
  | n + 1 => by
    rw [pow_succ, pow_succ', Ring.mul_inverse_rev' ((Commute.refl r).pow_left n),
      Ring.inverse_pow r n]
#align ring.inverse_pow Ring.inverse_pow

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero M] {n : ℕ} (hn : 0 < n)

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
  -- ⊢ x ^ n ∣ x ^ m → n ≤ m
  · intro h
    -- ⊢ n ≤ m
    rw [← not_lt]
    -- ⊢ ¬m < n
    intro hmn
    -- ⊢ False
    apply h1
    -- ⊢ IsUnit x
    have : x ^ m * x ∣ x ^ m * 1 := by
      rw [← pow_succ', mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    -- ⊢ x ^ m ≠ 0
    apply pow_ne_zero m h0
    -- 🎉 no goals
  · apply pow_dvd_pow
    -- 🎉 no goals
#align pow_dvd_pow_iff pow_dvd_pow_iff

section Semiring

variable [Semiring R] [Semiring S]

protected theorem RingHom.map_pow (f : R →+* S) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a
#align ring_hom.map_pow RingHom.map_pow

theorem min_pow_dvd_add {n m : ℕ} {a b c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) :
    c ^ min n m ∣ a + b := by
  replace ha := (pow_dvd_pow c (min_le_left n m)).trans ha
  -- ⊢ c ^ min n m ∣ a + b
  replace hb := (pow_dvd_pow c (min_le_right n m)).trans hb
  -- ⊢ c ^ min n m ∣ a + b
  exact dvd_add ha hb
  -- 🎉 no goals
#align min_pow_dvd_add min_pow_dvd_add

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem add_sq (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [sq, add_mul_self_eq]
  -- 🎉 no goals
#align add_sq add_sq

theorem add_sq' (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [add_sq, add_assoc, add_comm _ (b ^ 2), add_assoc]
  -- 🎉 no goals
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
                -- 🎉 no goals
    (fun h ↦ by rw [pow_succ, h, mul_one])
                -- 🎉 no goals
#align neg_one_pow_eq_or neg_one_pow_eq_or

variable {R}

theorem neg_pow (a : R) (n : ℕ) : (-a) ^ n = (-1) ^ n * a ^ n :=
  neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n
#align neg_pow neg_pow

section
set_option linter.deprecated false

theorem neg_pow_bit0 (a : R) (n : ℕ) : (-a) ^ bit0 n = a ^ bit0 n := by
  rw [pow_bit0', neg_mul_neg, pow_bit0']
  -- 🎉 no goals
#align neg_pow_bit0 neg_pow_bit0

@[simp]
theorem neg_pow_bit1 (a : R) (n : ℕ) : (-a) ^ bit1 n = -a ^ bit1 n := by
  simp only [bit1, pow_succ, neg_pow_bit0, neg_mul_eq_neg_mul]
  -- 🎉 no goals
#align neg_pow_bit1 neg_pow_bit1

end

theorem neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]
                                                -- 🎉 no goals
#align neg_sq neg_sq

-- Porting note: removed the simp attribute to please the simpNF linter
theorem neg_one_sq : (-1 : R) ^ 2 = 1 := by simp [neg_sq, one_pow]
                                            -- 🎉 no goals
#align neg_one_sq neg_one_sq

alias neg_pow_two := neg_sq
#align neg_pow_two neg_pow_two

alias neg_one_pow_two := neg_one_sq
#align neg_one_pow_two neg_one_pow_two

end HasDistribNeg

section Ring

variable [Ring R] {a b : R}

protected theorem Commute.sq_sub_sq (h : Commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, h.mul_self_sub_mul_self_eq]
  -- 🎉 no goals
#align commute.sq_sub_sq Commute.sq_sub_sq

@[simp]
theorem neg_one_pow_mul_eq_zero_iff {n : ℕ} {r : R} : (-1) ^ n * r = 0 ↔ r = 0 := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]
  -- ⊢ (-1) ^ n * r = 0 ↔ r = 0
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align neg_one_pow_mul_eq_zero_iff neg_one_pow_mul_eq_zero_iff

@[simp]
theorem mul_neg_one_pow_eq_zero_iff {n : ℕ} {r : R} : r * (-1) ^ n = 0 ↔ r = 0 := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]
  -- ⊢ r * (-1) ^ n = 0 ↔ r = 0
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align mul_neg_one_pow_eq_zero_iff mul_neg_one_pow_eq_zero_iff

variable [NoZeroDivisors R]

protected theorem Commute.sq_eq_sq_iff_eq_or_eq_neg (h : Commute a b) :
    a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm]
  -- 🎉 no goals
#align commute.sq_eq_sq_iff_eq_or_eq_neg Commute.sq_eq_sq_iff_eq_or_eq_neg

@[simp]
theorem sq_eq_one_iff : a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg, one_pow]
  -- 🎉 no goals
#align sq_eq_one_iff sq_eq_one_iff

theorem sq_ne_one_iff : a ^ 2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 :=
  sq_eq_one_iff.not.trans not_or
#align sq_ne_one_iff sq_ne_one_iff

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
  -- 🎉 no goals
#align sub_sq sub_sq

alias sub_pow_two := sub_sq
#align sub_pow_two sub_pow_two

theorem sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]
  -- 🎉 no goals
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
  -- 🎉 no goals
#align units.sq_eq_sq_iff_eq_or_eq_neg Units.sq_eq_sq_iff_eq_or_eq_neg

protected theorem eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
  Units.sq_eq_sq_iff_eq_or_eq_neg.1 h
#align units.eq_or_eq_neg_of_sq_eq_sq Units.eq_or_eq_neg_of_sq_eq_sq

end Units

end CommRing
