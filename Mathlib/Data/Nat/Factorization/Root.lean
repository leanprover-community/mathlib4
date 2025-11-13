/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Factorization.Defs

/-!
# Roots of natural numbers, rounded up and down

This file defines the flooring and ceiling root of a natural number.
`Nat.floorRoot n a`/`Nat.ceilRoot n a`, the `n`-th flooring/ceiling root of `a`, is the natural
number whose `p`-adic valuation is the floor/ceil of the `p`-adic valuation of `a`.

For example the `2`-nd flooring and ceiling roots of `2^3 * 3^2 * 5` are `2 * 3` and `2^2 * 3 * 5`
respectively. Note this is **not** the `n`-th root of `a` as a real number, rounded up or down.

These operations are respectively the right and left adjoints to the map `a ↦ a ^ n` where `ℕ` is
ordered by divisibility. This is useful because it lets us characterise the numbers `a` whose `n`-th
power divide `n` as the divisors of some fixed number (aka `floorRoot n b`). See
`Nat.pow_dvd_iff_dvd_floorRoot`. Similarly, it lets us characterise the `b` whose `n`-th power is a
multiple of `a` as the multiples of some fixed number (aka `ceilRoot n a`). See
`Nat.dvd_pow_iff_ceilRoot_dvd`.

## TODO

* `norm_num` extension
-/

open Finsupp

namespace Nat
variable {a b n : ℕ}

/-- Flooring root of a natural number. This divides the valuation of every prime number rounding
down.

Eg if `n = 2`, `a = 2^3 * 3^2 * 5`, then `floorRoot n a = 2 * 3`.

In order theory terms, this is the upper or right adjoint of the map `a ↦ a ^ n : ℕ → ℕ` where `ℕ`
is ordered by divisibility.

To ensure that the adjunction (`Nat.pow_dvd_iff_dvd_floorRoot`) holds in as many cases as possible,
we special-case the following values:
* `floorRoot 0 a = 0`
* `floorRoot n 0 = 0`
-/
def floorRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k ↦ p ^ (k / n)

/-- The RHS is a noncomputable version of `Nat.floorRoot` with better order-theoretic
properties. -/
lemma floorRoot_def :
    floorRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorization ⌊/⌋ n).prod (· ^ ·) := by
  unfold floorRoot; split_ifs with h <;> simp [Finsupp.floorDiv_def, prod_mapRange_index pow_zero]

@[simp] lemma floorRoot_zero_left (a : ℕ) : floorRoot 0 a = 0 := by simp [floorRoot]
@[simp] lemma floorRoot_zero_right (n : ℕ) : floorRoot n 0 = 0 := by simp [floorRoot]
@[simp] lemma floorRoot_one_left (a : ℕ) : floorRoot 1 a = a := by
  simp [floorRoot]; split_ifs <;> simp [*]
@[simp] lemma floorRoot_one_right (hn : n ≠ 0) : floorRoot n 1 = 1 := by simp [floorRoot, hn]

@[simp] lemma floorRoot_pow_self (hn : n ≠ 0) (a : ℕ) : floorRoot n (a ^ n) = a := by
  simp [floorRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]

lemma floorRoot_ne_zero : floorRoot n a ≠ 0 ↔ n ≠ 0 ∧ a ≠ 0 := by
  simp +contextual [floorRoot, not_or]

@[simp] lemma floorRoot_eq_zero : floorRoot n a = 0 ↔ n = 0 ∨ a = 0 :=
  floorRoot_ne_zero.not_right.trans <| by simp only [not_and_or, ne_eq, not_not]

@[simp] lemma factorization_floorRoot (n a : ℕ) :
    (floorRoot n a).factorization = a.factorization ⌊/⌋ n := by
  rw [floorRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  refine prod_pow_factorization_eq_self fun p hp ↦ ?_
  have : p.Prime ∧ p ∣ a ∧ ¬a = 0 := by simpa using support_floorDiv_subset hp
  exact this.1

/-- Galois connection between `a ↦ a ^ n : ℕ → ℕ` and `floorRoot n : ℕ → ℕ` where `ℕ` is ordered
by divisibility. -/
lemma pow_dvd_iff_dvd_floorRoot : a ^ n ∣ b ↔ a ∣ floorRoot n b := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  obtain rfl | ha := eq_or_ne a 0
  · simp [hn]
  rw [← factorization_le_iff_dvd (pow_ne_zero _ ha) hb,
    ← factorization_le_iff_dvd ha (floorRoot_ne_zero.2 ⟨hn, hb⟩), factorization_pow,
    factorization_floorRoot, le_floorDiv_iff_smul_le (β := ℕ →₀ ℕ) (pos_iff_ne_zero.2 hn)]

lemma floorRoot_pow_dvd : floorRoot n a ^ n ∣ a := pow_dvd_iff_dvd_floorRoot.2 dvd_rfl

/-- Ceiling root of a natural number. This divides the valuation of every prime number rounding up.

Eg if `n = 3`, `a = 2^4 * 3^2 * 5`, then `ceilRoot n a = 2^2 * 3 * 5`.

In order theory terms, this is the lower or left adjoint of the map `a ↦ a ^ n : ℕ → ℕ` where `ℕ`
is ordered by divisibility.

To ensure that the adjunction (`Nat.dvd_pow_iff_ceilRoot_dvd`) holds in as many cases as possible,
we special-case the following values:
* `ceilRoot 0 a = 0` (this one is not strictly necessary)
* `ceilRoot n 0 = 0`
-/
def ceilRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k ↦ p ^ ((k + n - 1) / n)

/-- The RHS is a noncomputable version of `Nat.ceilRoot` with better order-theoretic
properties. -/
lemma ceilRoot_def :
    ceilRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorization ⌈/⌉ n).prod (· ^ ·) := by
  unfold ceilRoot
  split_ifs with h <;>
    simp [Finsupp.ceilDiv_def, prod_mapRange_index pow_zero, Nat.ceilDiv_eq_add_pred_div]

@[simp] lemma ceilRoot_zero_left (a : ℕ) : ceilRoot 0 a = 0 := by simp [ceilRoot]
@[simp] lemma ceilRoot_zero_right (n : ℕ) : ceilRoot n 0 = 0 := by simp [ceilRoot]
@[simp] lemma ceilRoot_one_left (a : ℕ) : ceilRoot 1 a = a := by
  simp [ceilRoot]; split_ifs <;> simp [*]
@[simp] lemma ceilRoot_one_right (hn : n ≠ 0) : ceilRoot n 1 = 1 := by simp [ceilRoot, hn]

@[simp] lemma ceilRoot_pow_self (hn : n ≠ 0) (a : ℕ) : ceilRoot n (a ^ n) = a := by
  simp [ceilRoot_def, pos_iff_ne_zero.2, hn]; split_ifs <;> simp [*]

lemma ceilRoot_ne_zero : ceilRoot n a ≠ 0 ↔ n ≠ 0 ∧ a ≠ 0 := by
  simp +contextual [ceilRoot_def, not_or]

@[simp] lemma ceilRoot_eq_zero : ceilRoot n a = 0 ↔ n = 0 ∨ a = 0 :=
  ceilRoot_ne_zero.not_right.trans <| by simp only [not_and_or, ne_eq, not_not]

@[simp] lemma factorization_ceilRoot (n a : ℕ) :
    (ceilRoot n a).factorization = a.factorization ⌈/⌉ n := by
  rw [ceilRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  refine prod_pow_factorization_eq_self fun p hp ↦ ?_
  have : p.Prime ∧ p ∣ a ∧ ¬a = 0 := by simpa using support_ceilDiv_subset hp
  exact this.1

/-- Galois connection between `ceilRoot n : ℕ → ℕ` and `a ↦ a ^ n : ℕ → ℕ` where `ℕ` is ordered
by divisibility.

Note that this cannot possibly hold for `n = 0`, regardless of the value of `ceilRoot 0 a`, because
the statement reduces to `a = 1 ↔ ceilRoot 0 a ∣ b`, which is false for e.g. `a = 0`,
`b = ceilRoot 0 a`. -/
lemma dvd_pow_iff_ceilRoot_dvd (hn : n ≠ 0) : a ∣ b ^ n ↔ ceilRoot n a ∣ b := by
  obtain rfl | ha := eq_or_ne a 0
  · aesop
  obtain rfl | hb := eq_or_ne b 0
  · simp [hn]
  rw [← factorization_le_iff_dvd ha (pow_ne_zero _ hb),
    ← factorization_le_iff_dvd (ceilRoot_ne_zero.2 ⟨hn, ha⟩) hb, factorization_pow,
    factorization_ceilRoot, ceilDiv_le_iff_le_smul (β := ℕ →₀ ℕ) (pos_iff_ne_zero.2 hn)]

lemma dvd_ceilRoot_pow (hn : n ≠ 0) : a ∣ ceilRoot n a ^ n :=
  (dvd_pow_iff_ceilRoot_dvd hn).2 dvd_rfl

end Nat
