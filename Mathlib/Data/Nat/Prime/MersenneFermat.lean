/-
Copyright (c) 2024 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, Thomas Browning
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Primality of `a ^ n + 1`
-/

open Nat

/-- Prime `a ^ n + 1` implies `n` is a power of two. -/
theorem pow_of_pow_add_prime {a n : ℕ} (ha : 1 < a) (hn : n ≠ 0) (hP : (a ^ n + 1).Prime) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  have h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow, hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne', add_left_inj, pow_eq_self_iff ha] at h
  rw [h, mul_one]

/-!
# Primality of `a ^ n - 1`
-/

/-- Prime `a ^ n - 1` implies `a = 2` and prime `n`. -/
theorem prime_of_pow_sub_one_prime {a n : ℕ} (hn1 : n ≠ 1) (hP : (a ^ n - 1).Prime) :
    a = 2 ∧ n.Prime := by
  have han1 : 1 < a ^ n := tsub_pos_iff_lt.mp hP.pos
  have hn0 : n ≠ 0 := fun h ↦ (h ▸ han1).ne' rfl
  have ha1 : 1 < a := (Nat.one_lt_pow_iff hn0).mp han1
  have ha0 : 0 < a := one_pos.trans ha1
  have ha2 : a = 2 := by
    contrapose! hn1
    have h := nat_sub_dvd_pow_sub_pow a 1 n
    rw [one_pow, hP.dvd_iff_eq (mt (Nat.sub_eq_iff_eq_add ha1.le).mp hn1), eq_comm] at h
    exact (pow_eq_self_iff ha1).mp (Nat.sub_one_cancel ha0 (pow_pos ha0 n) h).symm
  subst ha2
  refine ⟨rfl, Nat.prime_def_lt''.mpr ⟨(two_le_iff n).mpr ⟨hn0, hn1⟩, fun d hdn ↦ ?_⟩⟩
  have hinj : ∀ x y, 2 ^ x - 1 = 2 ^ y - 1 → x = y :=
    fun x y h ↦ Nat.pow_right_injective le_rfl (sub_one_cancel (pow_pos ha0 x) (pow_pos ha0 y) h)
  have h := nat_sub_dvd_pow_sub_pow (2 ^ d) 1 (n / d)
  rw [one_pow, ← pow_mul, Nat.mul_div_cancel' hdn] at h
  exact (hP.eq_one_or_self_of_dvd (2 ^ d - 1) h).imp (hinj d 1) (hinj d n)
