/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Roots of natural numbers, rounded up and down

This file defines the flooring and ceiling root of a natural number. The `n`-th flooring/ceiling
root of `a` is the natural number whose `p`-adic valuation is the floor/ceil of the `p`-adic
valuation of `a`.

For example the `2`-nd flooring and ceiling roots of `2^3 * 3^2 * 5` are `2 * 3` and `2^2 * 3 * 5`
respectively. Note this is **not** the `n`-th root of `a` as a real number, rounded up or down.

Those operations are respectively the right and left adjoints to the map `a ↦ a ^ n` where `ℕ` is
ordered by divisibility.

## TODO

`norm_num` extension
-/

open Finsupp

namespace Nat
variable {a b n : ℕ}

/-- Flooring root of a natural number. This divides the valuation of every prime number rounding
down.

Eg if `n = 2`, `a = 2^3 * 3^2 * 5`, then `floorRoot n a = 2 * 3`.

In order theory terms, this is the upper or right adjoint of the map `a ↦ a ^ n`. -/
noncomputable def floorRoot (n a : ℕ) : ℕ := (a.factorization ⌊/⌋ n).prod (· ^ ·)

@[simp] lemma floorRoot_zero_left (a : ℕ) : floorRoot 0 a = 1 := by simp [floorRoot]
@[simp] lemma floorRoot_zero_right (n : ℕ) : floorRoot n 0 = 1 := by simp [floorRoot]
@[simp] lemma floorRoot_one_left (ha : a ≠ 0) : floorRoot 1 a = a := by simp [floorRoot, ha]
@[simp] lemma floorRoot_one_right (n : ℕ) : floorRoot n 1 = 1 := by simp [floorRoot]

@[simp] lemma floorRoot_pow_self (hn : n ≠ 0) (ha : a ≠ 0) : floorRoot n (a ^ n) = a := by
  simp [floorRoot, pos_iff_ne_zero.2 hn, ha]

@[simp] lemma floorRoot_ne_zero : floorRoot n a ≠ 0 := by
  simp (config := { contextual := true }) [floorRoot, not_imp_not]

@[simp] lemma factorization_floorRoot (n a : ℕ) :
    (floorRoot n a).factorization = a.factorization ⌊/⌋ n := by
  refine prod_pow_factorization_eq_self fun p hp ↦ ?_
  have : p.Prime ∧ _ := by simpa using support_floorDiv_subset hp
  exact this.1

lemma pow_dvd_iff (hn : n ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) : a ^ n ∣ b ↔ a ∣ floorRoot n b := by
  rw [← factorization_le_iff_dvd (pow_ne_zero _ ha) hb,
    ← factorization_le_iff_dvd ha floorRoot_ne_zero, factorization_pow, factorization_floorRoot,
    le_floorDiv_iff_smul_le (β := ℕ →₀ ℕ) (pos_iff_ne_zero.2 hn)]

lemma floorRoot_pow_dvd (hn : n ≠ 0) (ha : a ≠ 0) : floorRoot n a ^ n ∣ a :=
  (pow_dvd_iff hn floorRoot_ne_zero ha).2 dvd_rfl

/-- Ceiling root of a natural number. This divides the valuation of every prime number rounding up.

Eg if `n = 3`, `a = 2^4 * 3^2 * 5`, then `ceilRoot n a = 2^2 * 3 * 5`.

In order theory terms, this is the lower or left adjoint of the map `a ↦ a ^ n`. -/
noncomputable def ceilRoot (n a : ℕ) : ℕ := (a.factorization ⌈/⌉ n).prod (· ^ ·)

@[simp] lemma ceilRoot_zero_left (a : ℕ) : ceilRoot 0 a = 1 := by simp [ceilRoot]
@[simp] lemma ceilRoot_zero_right (n : ℕ) : ceilRoot n 0 = 1 := by simp [ceilRoot]
@[simp] lemma ceilRoot_one_left (ha : a ≠ 0) : ceilRoot 1 a = a := by simp [ceilRoot, ha]
@[simp] lemma ceilRoot_one_right (n : ℕ) : ceilRoot n 1 = 1 := by simp [ceilRoot]

@[simp] lemma ceilRoot_pow_self (hn : n ≠ 0) (ha : a ≠ 0) : ceilRoot n (a ^ n) = a := by
  simp [ceilRoot, pos_iff_ne_zero.2 hn, ha]

@[simp] lemma ceilRoot_ne_zero : ceilRoot n a ≠ 0 := by
  simp (config := { contextual := true }) [ceilRoot, not_imp_not]

@[simp] lemma factorization_ceilRoot (n a : ℕ) :
    (ceilRoot n a).factorization = a.factorization ⌈/⌉ n := by
  refine prod_pow_factorization_eq_self fun p hp ↦ ?_
  have : p.Prime ∧ _ := by simpa using support_ceilDiv_subset hp
  exact this.1

lemma dvd_pow_iff (hn : n ≠ 0) (ha : a ≠ 0) : a ∣ b ^ n ↔ ceilRoot n a ∣ b := by
  obtain rfl | hb := eq_or_ne b 0
  · simp [hn]
  rw [← factorization_le_iff_dvd ha (pow_ne_zero _ hb),
    ← factorization_le_iff_dvd ceilRoot_ne_zero hb, factorization_pow, factorization_ceilRoot,
    ceilDiv_le_iff_le_smul (β := ℕ →₀ ℕ) (pos_iff_ne_zero.2 hn)]

lemma dvd_ceilRoot_pow (hn : n ≠ 0) (ha : a ≠ 0) : a ∣ ceilRoot n a ^ n :=
  (dvd_pow_iff hn ha).2 dvd_rfl

end Nat
