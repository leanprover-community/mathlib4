/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of continuum

In this file we define `Cardinal.continuum` (notation: `𝔠`, localized in `Cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `Cardinal.continuum` in scope `Cardinal`.
-/


namespace Cardinal

universe u v

open Cardinal

/-- Cardinality of the continuum. -/
def continuum : Cardinal.{u} :=
  2 ^ ℵ₀

@[inherit_doc] scoped notation "𝔠" => Cardinal.continuum

@[simp]
theorem two_power_aleph0 : 2 ^ ℵ₀ = 𝔠 :=
  rfl

@[simp]
theorem lift_continuum : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph0, lift_two_power, lift_aleph0, two_power_aleph0]

@[simp]
theorem continuum_le_lift {c : Cardinal.{u}} : 𝔠 ≤ lift.{v} c ↔ 𝔠 ≤ c := by
  rw [← lift_continuum.{v, u}, lift_le]

@[simp]
theorem lift_le_continuum {c : Cardinal.{u}} : lift.{v} c ≤ 𝔠 ↔ c ≤ 𝔠 := by
  rw [← lift_continuum.{v, u}, lift_le]

@[simp]
theorem continuum_lt_lift {c : Cardinal.{u}} : 𝔠 < lift.{v} c ↔ 𝔠 < c := by
  rw [← lift_continuum.{v, u}, lift_lt]

@[simp]
theorem lift_lt_continuum {c : Cardinal.{u}} : lift.{v} c < 𝔠 ↔ c < 𝔠 := by
  rw [← lift_continuum.{v, u}, lift_lt]

/-!
### Inequalities
-/


theorem aleph0_lt_continuum : ℵ₀ < 𝔠 :=
  cantor ℵ₀

theorem aleph0_le_continuum : ℵ₀ ≤ 𝔠 :=
  aleph0_lt_continuum.le

@[simp]
theorem beth_one : ℶ_ 1 = 𝔠 := by simpa using beth_succ 0

theorem nat_lt_continuum (n : ℕ) : ↑n < 𝔠 :=
  (nat_lt_aleph0 n).trans aleph0_lt_continuum

theorem mk_set_nat : #(Set ℕ) = 𝔠 := by simp

theorem continuum_pos : 0 < 𝔠 :=
  nat_lt_continuum 0

theorem continuum_ne_zero : 𝔠 ≠ 0 :=
  continuum_pos.ne'

theorem aleph_one_le_continuum : ℵ₁ ≤ 𝔠 := by
  rw [← succ_aleph0]
  exact Order.succ_le_of_lt aleph0_lt_continuum

@[simp]
theorem continuum_toNat : toNat continuum = 0 :=
  toNat_apply_of_aleph0_le aleph0_le_continuum

@[simp]
theorem continuum_toENat : toENat continuum = ⊤ :=
  (toENat_eq_top.2 aleph0_le_continuum)

/-!
### Addition
-/


@[simp]
theorem aleph0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum aleph0_le_continuum

@[simp]
theorem continuum_add_aleph0 : 𝔠 + ℵ₀ = 𝔠 :=
  (add_comm _ _).trans aleph0_add_continuum

@[simp]
theorem continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
  add_eq_self aleph0_le_continuum

@[simp]
theorem nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
  nat_add_eq n aleph0_le_continuum

@[simp]
theorem continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
  (add_comm _ _).trans (nat_add_continuum n)

@[simp]
theorem ofNat_add_continuum {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) + 𝔠 = 𝔠 :=
  nat_add_continuum n

@[simp]
theorem continuum_add_ofNat {n : ℕ} [Nat.AtLeastTwo n] : 𝔠 + ofNat(n) = 𝔠 :=
  continuum_add_nat n

/-!
### Multiplication
-/


@[simp]
theorem continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
  mul_eq_left aleph0_le_continuum le_rfl continuum_ne_zero

@[simp]
theorem continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠 :=
  mul_eq_left aleph0_le_continuum aleph0_le_continuum aleph0_ne_zero

@[simp]
theorem aleph0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
  (mul_comm _ _).trans continuum_mul_aleph0

@[simp]
theorem nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
  mul_eq_right aleph0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)

@[simp]
theorem continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
  (mul_comm _ _).trans (nat_mul_continuum hn)

@[simp]
theorem ofNat_mul_continuum {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) * 𝔠 = 𝔠 :=
  nat_mul_continuum (OfNat.ofNat_ne_zero n)

@[simp]
theorem continuum_mul_ofNat {n : ℕ} [Nat.AtLeastTwo n] : 𝔠 * ofNat(n) = 𝔠 :=
  continuum_mul_nat (OfNat.ofNat_ne_zero n)

/-!
### Power
-/


@[simp]
theorem aleph0_power_aleph0 : ℵ₀ ^ ℵ₀ = 𝔠 :=
  power_self_eq le_rfl

@[simp]
theorem nat_power_aleph0 {n : ℕ} (hn : 2 ≤ n) : n ^ ℵ₀ = 𝔠 :=
  nat_power_eq le_rfl hn

@[simp]
theorem continuum_power_aleph0 : 𝔠 ^ ℵ₀ = 𝔠 := by
  rw [← two_power_aleph0, ← power_mul, mul_eq_left le_rfl le_rfl aleph0_ne_zero]

theorem power_aleph0_of_le_continuum {x : Cardinal} (h₁ : 2 ≤ x) (h₂ : x ≤ 𝔠) : x ^ ℵ₀ = 𝔠 := by
  apply le_antisymm
  · rw [← continuum_power_aleph0]
    exact power_le_power_right h₂
  · rw [← two_power_aleph0]
    exact power_le_power_right h₁

end Cardinal
