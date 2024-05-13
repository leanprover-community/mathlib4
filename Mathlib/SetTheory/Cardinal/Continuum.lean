/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.SetTheory.Cardinal.Ordinal

#align_import set_theory.cardinal.continuum from "leanprover-community/mathlib"@"e08a42b2dd544cf11eba72e5fc7bf199d4349925"

/-!
# Cardinality of continuum

In this file we define `Cardinal.continuum` (notation: `𝔠`, localized in `Cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `Cardinal.continuum` in locale `Cardinal`.
-/


namespace Cardinal

universe u v

open Cardinal

/-- Cardinality of continuum. -/
def continuum : Cardinal.{u} :=
  2 ^ ℵ₀
#align cardinal.continuum Cardinal.continuum

scoped notation "𝔠" => Cardinal.continuum

@[simp]
lemma two_power_aleph0 : 2 ^ aleph0.{u} = continuum.{u} :=
  rfl
#align cardinal.two_power_aleph_0 Cardinal.two_power_aleph0

@[simp]
lemma lift_continuum : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph0, lift_two_power, lift_aleph0, two_power_aleph0]
#align cardinal.lift_continuum Cardinal.lift_continuum

@[simp]
lemma continuum_le_lift {c : Cardinal.{u}} : 𝔠 ≤ lift.{v} c ↔ 𝔠 ≤ c := by
  -- Porting note: added explicit universes
  rw [← lift_continuum.{u,v}, lift_le]
#align cardinal.continuum_le_lift Cardinal.continuum_le_lift

@[simp]
lemma lift_le_continuum {c : Cardinal.{u}} : lift.{v} c ≤ 𝔠 ↔ c ≤ 𝔠 := by
  -- Porting note: added explicit universes
  rw [← lift_continuum.{u,v}, lift_le]
#align cardinal.lift_le_continuum Cardinal.lift_le_continuum

@[simp]
lemma continuum_lt_lift {c : Cardinal.{u}} : 𝔠 < lift.{v} c ↔ 𝔠 < c := by
  -- Porting note: added explicit universes
  rw [← lift_continuum.{u,v}, lift_lt]
#align cardinal.continuum_lt_lift Cardinal.continuum_lt_lift

@[simp]
lemma lift_lt_continuum {c : Cardinal.{u}} : lift.{v} c < 𝔠 ↔ c < 𝔠 := by
  -- Porting note: added explicit universes
  rw [← lift_continuum.{u,v}, lift_lt]
#align cardinal.lift_lt_continuum Cardinal.lift_lt_continuum

/-!
### Inequalities
-/


lemma aleph0_lt_continuum : ℵ₀ < 𝔠 :=
  cantor ℵ₀
#align cardinal.aleph_0_lt_continuum Cardinal.aleph0_lt_continuum

lemma aleph0_le_continuum : ℵ₀ ≤ 𝔠 :=
  aleph0_lt_continuum.le
#align cardinal.aleph_0_le_continuum Cardinal.aleph0_le_continuum

@[simp]
lemma beth_one : beth 1 = 𝔠 := by simpa using beth_succ 0
#align cardinal.beth_one Cardinal.beth_one

lemma nat_lt_continuum (n : ℕ) : ↑n < 𝔠 :=
  (nat_lt_aleph0 n).trans aleph0_lt_continuum
#align cardinal.nat_lt_continuum Cardinal.nat_lt_continuum

lemma mk_set_nat : #(Set ℕ) = 𝔠 := by simp
#align cardinal.mk_set_nat Cardinal.mk_set_nat

lemma continuum_pos : 0 < 𝔠 :=
  nat_lt_continuum 0
#align cardinal.continuum_pos Cardinal.continuum_pos

lemma continuum_ne_zero : 𝔠 ≠ 0 :=
  continuum_pos.ne'
#align cardinal.continuum_ne_zero Cardinal.continuum_ne_zero

lemma aleph_one_le_continuum : aleph 1 ≤ 𝔠 := by
  rw [← succ_aleph0]
  exact Order.succ_le_of_lt aleph0_lt_continuum
#align cardinal.aleph_one_le_continuum Cardinal.aleph_one_le_continuum

@[simp]
lemma continuum_toNat : toNat continuum = 0 :=
  toNat_apply_of_aleph0_le aleph0_le_continuum
#align cardinal.continuum_to_nat Cardinal.continuum_toNat

@[simp]
lemma continuum_toPartENat : toPartENat continuum = ⊤ :=
  toPartENat_apply_of_aleph0_le aleph0_le_continuum
#align cardinal.continuum_to_part_enat Cardinal.continuum_toPartENat

/-!
### Addition
-/


@[simp]
lemma aleph0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum aleph0_le_continuum
#align cardinal.aleph_0_add_continuum Cardinal.aleph0_add_continuum

@[simp]
lemma continuum_add_aleph0 : 𝔠 + ℵ₀ = 𝔠 :=
  (add_comm _ _).trans aleph0_add_continuum
#align cardinal.continuum_add_aleph_0 Cardinal.continuum_add_aleph0

@[simp]
lemma continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
  add_eq_self aleph0_le_continuum
#align cardinal.continuum_add_self Cardinal.continuum_add_self

@[simp]
lemma nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
  nat_add_eq n aleph0_le_continuum
#align cardinal.nat_add_continuum Cardinal.nat_add_continuum

@[simp]
lemma continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
  (add_comm _ _).trans (nat_add_continuum n)
#align cardinal.continuum_add_nat Cardinal.continuum_add_nat

-- See note [no_index around OfNat.ofNat]
@[simp]
lemma ofNat_add_continuum {n : ℕ} [Nat.AtLeastTwo n] : no_index (OfNat.ofNat n) + 𝔠 = 𝔠 :=
  nat_add_continuum n

-- See note [no_index around OfNat.ofNat]
@[simp]
lemma continuum_add_ofNat {n : ℕ} [Nat.AtLeastTwo n] : 𝔠 + no_index (OfNat.ofNat n) = 𝔠 :=
  continuum_add_nat n

/-!
### Multiplication
-/


@[simp]
lemma continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
  mul_eq_left aleph0_le_continuum le_rfl continuum_ne_zero
#align cardinal.continuum_mul_self Cardinal.continuum_mul_self

@[simp]
lemma continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠 :=
  mul_eq_left aleph0_le_continuum aleph0_le_continuum aleph0_ne_zero
#align cardinal.continuum_mul_aleph_0 Cardinal.continuum_mul_aleph0

@[simp]
lemma aleph0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
  (mul_comm _ _).trans continuum_mul_aleph0
#align cardinal.aleph_0_mul_continuum Cardinal.aleph0_mul_continuum

@[simp]
lemma nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
  mul_eq_right aleph0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)
#align cardinal.nat_mul_continuum Cardinal.nat_mul_continuum

@[simp]
lemma continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
  (mul_comm _ _).trans (nat_mul_continuum hn)
#align cardinal.continuum_mul_nat Cardinal.continuum_mul_nat

-- See note [no_index around OfNat.ofNat]
@[simp]
lemma ofNat_mul_continuum {n : ℕ} [Nat.AtLeastTwo n] : no_index (OfNat.ofNat n) * 𝔠 = 𝔠 :=
  nat_mul_continuum (OfNat.ofNat_ne_zero n)

-- See note [no_index around OfNat.ofNat]
@[simp]
lemma continuum_mul_ofNat {n : ℕ} [Nat.AtLeastTwo n] : 𝔠 * no_index (OfNat.ofNat n) = 𝔠 :=
  continuum_mul_nat (OfNat.ofNat_ne_zero n)

/-!
### Power
-/


@[simp]
lemma aleph0_power_aleph0 : aleph0.{u} ^ aleph0.{u} = 𝔠 :=
  power_self_eq le_rfl
#align cardinal.aleph_0_power_aleph_0 Cardinal.aleph0_power_aleph0

@[simp]
lemma nat_power_aleph0 {n : ℕ} (hn : 2 ≤ n) : (n ^ aleph0.{u} : Cardinal.{u}) = 𝔠 :=
  nat_power_eq le_rfl hn
#align cardinal.nat_power_aleph_0 Cardinal.nat_power_aleph0

@[simp]
lemma continuum_power_aleph0 : continuum.{u} ^ aleph0.{u} = 𝔠 := by
  rw [← two_power_aleph0, ← power_mul, mul_eq_left le_rfl le_rfl aleph0_ne_zero]
#align cardinal.continuum_power_aleph_0 Cardinal.continuum_power_aleph0

end Cardinal
