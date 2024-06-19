/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import Mathlib.Data.Nat.Prime
import Mathlib.Data.PNat.Basic

#align_import data.pnat.prime from "leanprover-community/mathlib"@"09597669f02422ed388036273d8848119699c22f"

/-!
# Primality and GCD on pnat

This file extends the theory of `ℕ+` with `gcd`, `lcm` and `Prime` functions, analogous to those on
`Nat`.
-/


namespace Nat.Primes

-- Porting note (#11445): new definition
/-- The canonical map from `Nat.Primes` to `ℕ+` -/
@[coe] def toPNat : Nat.Primes → ℕ+ :=
  fun p => ⟨(p : ℕ), p.property.pos⟩

instance coePNat : Coe Nat.Primes ℕ+ :=
  ⟨toPNat⟩
#align nat.primes.coe_pnat Nat.Primes.coePNat

@[norm_cast]
theorem coe_pnat_nat (p : Nat.Primes) : ((p : ℕ+) : ℕ) = p :=
  rfl
#align nat.primes.coe_pnat_nat Nat.Primes.coe_pnat_nat

theorem coe_pnat_injective : Function.Injective ((↑) : Nat.Primes → ℕ+) := fun p q h =>
  Subtype.ext (by injection h)
#align nat.primes.coe_pnat_injective Nat.Primes.coe_pnat_injective

@[norm_cast]
theorem coe_pnat_inj (p q : Nat.Primes) : (p : ℕ+) = (q : ℕ+) ↔ p = q :=
  coe_pnat_injective.eq_iff
#align nat.primes.coe_pnat_inj Nat.Primes.coe_pnat_inj

end Nat.Primes

namespace PNat

open Nat

/-- The greatest common divisor (gcd) of two positive natural numbers,
  viewed as positive natural number. -/
def gcd (n m : ℕ+) : ℕ+ :=
  ⟨Nat.gcd (n : ℕ) (m : ℕ), Nat.gcd_pos_of_pos_left (m : ℕ) n.pos⟩
#align pnat.gcd PNat.gcd

/-- The least common multiple (lcm) of two positive natural numbers,
  viewed as positive natural number. -/
def lcm (n m : ℕ+) : ℕ+ :=
  ⟨Nat.lcm (n : ℕ) (m : ℕ), by
    let h := mul_pos n.pos m.pos
    rw [← gcd_mul_lcm (n : ℕ) (m : ℕ), mul_comm] at h
    exact pos_of_dvd_of_pos (Dvd.intro (Nat.gcd (n : ℕ) (m : ℕ)) rfl) h⟩
#align pnat.lcm PNat.lcm

@[simp, norm_cast]
theorem gcd_coe (n m : ℕ+) : (gcd n m : ℕ) = Nat.gcd n m :=
  rfl
#align pnat.gcd_coe PNat.gcd_coe

@[simp, norm_cast]
theorem lcm_coe (n m : ℕ+) : (lcm n m : ℕ) = Nat.lcm n m :=
  rfl
#align pnat.lcm_coe PNat.lcm_coe

theorem gcd_dvd_left (n m : ℕ+) : gcd n m ∣ n :=
  dvd_iff.2 (Nat.gcd_dvd_left (n : ℕ) (m : ℕ))
#align pnat.gcd_dvd_left PNat.gcd_dvd_left

theorem gcd_dvd_right (n m : ℕ+) : gcd n m ∣ m :=
  dvd_iff.2 (Nat.gcd_dvd_right (n : ℕ) (m : ℕ))
#align pnat.gcd_dvd_right PNat.gcd_dvd_right

theorem dvd_gcd {m n k : ℕ+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n :=
  dvd_iff.2 (Nat.dvd_gcd (dvd_iff.1 hm) (dvd_iff.1 hn))
#align pnat.dvd_gcd PNat.dvd_gcd

theorem dvd_lcm_left (n m : ℕ+) : n ∣ lcm n m :=
  dvd_iff.2 (Nat.dvd_lcm_left (n : ℕ) (m : ℕ))
#align pnat.dvd_lcm_left PNat.dvd_lcm_left

theorem dvd_lcm_right (n m : ℕ+) : m ∣ lcm n m :=
  dvd_iff.2 (Nat.dvd_lcm_right (n : ℕ) (m : ℕ))
#align pnat.dvd_lcm_right PNat.dvd_lcm_right

theorem lcm_dvd {m n k : ℕ+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k :=
  dvd_iff.2 (@Nat.lcm_dvd (m : ℕ) (n : ℕ) (k : ℕ) (dvd_iff.1 hm) (dvd_iff.1 hn))
#align pnat.lcm_dvd PNat.lcm_dvd

theorem gcd_mul_lcm (n m : ℕ+) : gcd n m * lcm n m = n * m :=
  Subtype.eq (Nat.gcd_mul_lcm (n : ℕ) (m : ℕ))
#align pnat.gcd_mul_lcm PNat.gcd_mul_lcm

theorem eq_one_of_lt_two {n : ℕ+} : n < 2 → n = 1 := by
  intro h; apply le_antisymm; swap
  · apply PNat.one_le
  · exact PNat.lt_add_one_iff.1 h
#align pnat.eq_one_of_lt_two PNat.eq_one_of_lt_two

section Prime

/-! ### Prime numbers -/


/-- Primality predicate for `ℕ+`, defined in terms of `Nat.Prime`. -/
def Prime (p : ℕ+) : Prop :=
  (p : ℕ).Prime
#align pnat.prime PNat.Prime

theorem Prime.one_lt {p : ℕ+} : p.Prime → 1 < p :=
  Nat.Prime.one_lt
#align pnat.prime.one_lt PNat.Prime.one_lt

theorem prime_two : (2 : ℕ+).Prime :=
  Nat.prime_two
#align pnat.prime_two PNat.prime_two

instance {p : ℕ+} [h : Fact p.Prime] : Fact (p : ℕ).Prime := h

instance fact_prime_two : Fact (2 : ℕ+).Prime :=
  ⟨prime_two⟩

theorem prime_three : (3 : ℕ+).Prime :=
  Nat.prime_three

instance fact_prime_three : Fact (3 : ℕ+).Prime :=
  ⟨prime_three⟩

theorem prime_five : (5 : ℕ+).Prime :=
  Nat.prime_five

instance fact_prime_five : Fact (5 : ℕ+).Prime :=
  ⟨prime_five⟩

theorem dvd_prime {p m : ℕ+} (pp : p.Prime) : m ∣ p ↔ m = 1 ∨ m = p := by
  rw [PNat.dvd_iff]
  rw [Nat.dvd_prime pp]
  simp
#align pnat.dvd_prime PNat.dvd_prime

theorem Prime.ne_one {p : ℕ+} : p.Prime → p ≠ 1 := by
  intro pp
  intro contra
  apply Nat.Prime.ne_one pp
  rw [PNat.coe_eq_one_iff]
  apply contra
#align pnat.prime.ne_one PNat.Prime.ne_one

@[simp]
theorem not_prime_one : ¬(1 : ℕ+).Prime :=
  Nat.not_prime_one
#align pnat.not_prime_one PNat.not_prime_one

theorem Prime.not_dvd_one {p : ℕ+} : p.Prime → ¬p ∣ 1 := fun pp : p.Prime => by
  rw [dvd_iff]
  apply Nat.Prime.not_dvd_one pp
#align pnat.prime.not_dvd_one PNat.Prime.not_dvd_one

theorem exists_prime_and_dvd {n : ℕ+} (hn : n ≠ 1) : ∃ p : ℕ+, p.Prime ∧ p ∣ n := by
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (mt coe_eq_one_iff.mp hn)
  exists (⟨p, Nat.Prime.pos hp.left⟩ : ℕ+); rw [dvd_iff]; apply hp
#align pnat.exists_prime_and_dvd PNat.exists_prime_and_dvd

end Prime

section Coprime

/-! ### Coprime numbers and gcd -/


/-- Two pnats are coprime if their gcd is 1. -/
def Coprime (m n : ℕ+) : Prop :=
  m.gcd n = 1
#align pnat.coprime PNat.Coprime

@[simp, norm_cast]
theorem coprime_coe {m n : ℕ+} : Nat.Coprime ↑m ↑n ↔ m.Coprime n := by
  unfold Nat.Coprime Coprime
  rw [← coe_inj]
  simp
#align pnat.coprime_coe PNat.coprime_coe

theorem Coprime.mul {k m n : ℕ+} : m.Coprime k → n.Coprime k → (m * n).Coprime k := by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul
#align pnat.coprime.mul PNat.Coprime.mul

theorem Coprime.mul_right {k m n : ℕ+} : k.Coprime m → k.Coprime n → k.Coprime (m * n) := by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_right
#align pnat.coprime.mul_right PNat.Coprime.mul_right

theorem gcd_comm {m n : ℕ+} : m.gcd n = n.gcd m := by
  apply eq
  simp only [gcd_coe]
  apply Nat.gcd_comm
#align pnat.gcd_comm PNat.gcd_comm

theorem gcd_eq_left_iff_dvd {m n : ℕ+} : m ∣ n ↔ m.gcd n = m := by
  rw [dvd_iff]
  rw [Nat.gcd_eq_left_iff_dvd]
  rw [← coe_inj]
  simp
#align pnat.gcd_eq_left_iff_dvd PNat.gcd_eq_left_iff_dvd

theorem gcd_eq_right_iff_dvd {m n : ℕ+} : m ∣ n ↔ n.gcd m = m := by
  rw [gcd_comm]
  apply gcd_eq_left_iff_dvd
#align pnat.gcd_eq_right_iff_dvd PNat.gcd_eq_right_iff_dvd

theorem Coprime.gcd_mul_left_cancel (m : ℕ+) {n k : ℕ+} :
    k.Coprime n → (k * m).gcd n = m.gcd n := by
  intro h; apply eq; simp only [gcd_coe, mul_coe]
  apply Nat.Coprime.gcd_mul_left_cancel; simpa
#align pnat.coprime.gcd_mul_left_cancel PNat.Coprime.gcd_mul_left_cancel

theorem Coprime.gcd_mul_right_cancel (m : ℕ+) {n k : ℕ+} :
    k.Coprime n → (m * k).gcd n = m.gcd n := by rw [mul_comm]; apply Coprime.gcd_mul_left_cancel
#align pnat.coprime.gcd_mul_right_cancel PNat.Coprime.gcd_mul_right_cancel

theorem Coprime.gcd_mul_left_cancel_right (m : ℕ+) {n k : ℕ+} :
    k.Coprime m → m.gcd (k * n) = m.gcd n := by
  intro h; iterate 2 rw [gcd_comm]; symm;
  apply Coprime.gcd_mul_left_cancel _ h
#align pnat.coprime.gcd_mul_left_cancel_right PNat.Coprime.gcd_mul_left_cancel_right

theorem Coprime.gcd_mul_right_cancel_right (m : ℕ+) {n k : ℕ+} :
    k.Coprime m → m.gcd (n * k) = m.gcd n := by
  rw [mul_comm];
  apply Coprime.gcd_mul_left_cancel_right
#align pnat.coprime.gcd_mul_right_cancel_right PNat.Coprime.gcd_mul_right_cancel_right

@[simp]
theorem one_gcd {n : ℕ+} : gcd 1 n = 1 := by
  rw [← gcd_eq_left_iff_dvd]
  apply one_dvd
#align pnat.one_gcd PNat.one_gcd

@[simp]
theorem gcd_one {n : ℕ+} : gcd n 1 = 1 := by
  rw [gcd_comm]
  apply one_gcd
#align pnat.gcd_one PNat.gcd_one

@[symm]
theorem Coprime.symm {m n : ℕ+} : m.Coprime n → n.Coprime m := by
  unfold Coprime
  rw [gcd_comm]
  simp
#align pnat.coprime.symm PNat.Coprime.symm

@[simp]
theorem one_coprime {n : ℕ+} : (1 : ℕ+).Coprime n :=
  one_gcd
#align pnat.one_coprime PNat.one_coprime

@[simp]
theorem coprime_one {n : ℕ+} : n.Coprime 1 :=
  Coprime.symm one_coprime
#align pnat.coprime_one PNat.coprime_one

theorem Coprime.coprime_dvd_left {m k n : ℕ+} : m ∣ k → k.Coprime n → m.Coprime n := by
  rw [dvd_iff]
  repeat rw [← coprime_coe]
  apply Nat.Coprime.coprime_dvd_left
#align pnat.coprime.coprime_dvd_left PNat.Coprime.coprime_dvd_left

theorem Coprime.factor_eq_gcd_left {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) :
    a = (a * b).gcd m := by
  rw [gcd_eq_left_iff_dvd] at am
  conv_lhs => rw [← am]
  rw [eq_comm]
  apply Coprime.gcd_mul_right_cancel a
  apply Coprime.coprime_dvd_left bn cop.symm
#align pnat.coprime.factor_eq_gcd_left PNat.Coprime.factor_eq_gcd_left

theorem Coprime.factor_eq_gcd_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) :
    a = (b * a).gcd m := by rw [mul_comm]; apply Coprime.factor_eq_gcd_left cop am bn
#align pnat.coprime.factor_eq_gcd_right PNat.Coprime.factor_eq_gcd_right

theorem Coprime.factor_eq_gcd_left_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m)
    (bn : b ∣ n) : a = m.gcd (a * b) := by rw [gcd_comm]; apply Coprime.factor_eq_gcd_left cop am bn
#align pnat.coprime.factor_eq_gcd_left_right PNat.Coprime.factor_eq_gcd_left_right

theorem Coprime.factor_eq_gcd_right_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m)
    (bn : b ∣ n) : a = m.gcd (b * a) := by
  rw [gcd_comm]
  apply Coprime.factor_eq_gcd_right cop am bn
#align pnat.coprime.factor_eq_gcd_right_right PNat.Coprime.factor_eq_gcd_right_right

theorem Coprime.gcd_mul (k : ℕ+) {m n : ℕ+} (h : m.Coprime n) :
    k.gcd (m * n) = k.gcd m * k.gcd n := by
  rw [← coprime_coe] at h; apply eq
  simp only [gcd_coe, mul_coe]; apply Nat.Coprime.gcd_mul k h
#align pnat.coprime.gcd_mul PNat.Coprime.gcd_mul

theorem gcd_eq_left {m n : ℕ+} : m ∣ n → m.gcd n = m := by
  rw [dvd_iff]
  intro h
  apply eq
  simp only [gcd_coe]
  apply Nat.gcd_eq_left h
#align pnat.gcd_eq_left PNat.gcd_eq_left

theorem Coprime.pow {m n : ℕ+} (k l : ℕ) (h : m.Coprime n) : (m ^ k : ℕ).Coprime (n ^ l) := by
  rw [← coprime_coe] at *; apply Nat.Coprime.pow; apply h
#align pnat.coprime.pow PNat.Coprime.pow

end Coprime

end PNat
