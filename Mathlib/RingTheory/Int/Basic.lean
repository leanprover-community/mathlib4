/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Basic

/-!
# Divisibility over ℕ and ℤ

This file collects results for the integers and natural numbers that use ring theory in
their proofs or cases of ℕ and ℤ being examples of structures in ring theory.

## Main statements

* `Nat.factors_eq`: the multiset of elements of `Nat.factors` is equal to the factors
   given by the `UniqueFactorizationMonoid` instance

## Tags

prime, irreducible, natural numbers, integers, normalization monoid, gcd monoid,
greatest common divisor, prime factorization, prime factors, unique factorization,
unique factors
-/

namespace Int


theorem gcd_eq_one_iff_coprime {a b : ℤ} : Int.gcd a b = 1 ↔ IsCoprime a b := by
  constructor
  · intro hg
    obtain ⟨ua, -, ha⟩ := exists_unit_of_abs a
    obtain ⟨ub, -, hb⟩ := exists_unit_of_abs b
    use Nat.gcdA (Int.natAbs a) (Int.natAbs b) * ua, Nat.gcdB (Int.natAbs a) (Int.natAbs b) * ub
    rw [mul_assoc, ← ha, mul_assoc, ← hb, mul_comm, mul_comm _ (Int.natAbs b : ℤ), ←
      Nat.gcd_eq_gcd_ab, ← gcd_eq_natAbs, hg, Int.ofNat_one]
  · rintro ⟨r, s, h⟩
    by_contra hg
    obtain ⟨p, ⟨hp, ha, hb⟩⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    apply Nat.Prime.not_dvd_one hp
    rw [← natCast_dvd_natCast, Int.ofNat_one, ← h]
    exact dvd_add ((natCast_dvd.mpr ha).mul_left _) ((natCast_dvd.mpr hb).mul_left _)

theorem coprime_iff_nat_coprime {a b : ℤ} : IsCoprime a b ↔ Nat.Coprime a.natAbs b.natAbs := by
  rw [← gcd_eq_one_iff_coprime, Nat.coprime_iff_gcd_eq_one, gcd_eq_natAbs]

/-- If `gcd a (m * n) ≠ 1`, then `gcd a m ≠ 1` or `gcd a n ≠ 1`. -/
theorem gcd_ne_one_iff_gcd_mul_right_ne_one {a : ℤ} {m n : ℕ} :
    a.gcd (m * n) ≠ 1 ↔ a.gcd m ≠ 1 ∨ a.gcd n ≠ 1 := by
  simp only [gcd_eq_one_iff_coprime, ← not_and_or, not_iff_not, IsCoprime.mul_right_iff]

theorem sq_of_gcd_eq_one {a b c : ℤ} (h : Int.gcd a b = 1) (heq : a * b = c ^ 2) :
    ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2 := by
  have h' : IsUnit (GCDMonoid.gcd a b) := by
    rw [← coe_gcd, h, Int.ofNat_one]
    exact isUnit_one
  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h' heq
  use d
  rw [← hu]
  cases' Int.units_eq_one_or u with hu' hu' <;>
    · rw [hu']
      simp

theorem sq_of_coprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 2) :
    ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2 :=
  sq_of_gcd_eq_one (gcd_eq_one_iff_coprime.mpr h) heq

theorem natAbs_euclideanDomain_gcd (a b : ℤ) :
    Int.natAbs (EuclideanDomain.gcd a b) = Int.gcd a b := by
  apply Nat.dvd_antisymm <;> rw [← Int.natCast_dvd_natCast]
  · rw [Int.natAbs_dvd]
    exact Int.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
  · rw [Int.dvd_natAbs]
    exact EuclideanDomain.dvd_gcd Int.gcd_dvd_left Int.gcd_dvd_right

end Int

theorem Int.Prime.dvd_mul {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) :
    p ∣ m.natAbs ∨ p ∣ n.natAbs := by
  rwa [← hp.dvd_mul, ← Int.natAbs_mul, ← Int.natCast_dvd]

theorem Int.Prime.dvd_mul' {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) :
    (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n := by
  rw [Int.natCast_dvd, Int.natCast_dvd]
  exact Int.Prime.dvd_mul hp h

theorem Int.Prime.dvd_pow {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ k) :
    p ∣ n.natAbs := by
  rw [Int.natCast_dvd, Int.natAbs_pow] at h
  exact hp.dvd_of_dvd_pow h

theorem Int.Prime.dvd_pow' {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ k) :
    (p : ℤ) ∣ n := by
  rw [Int.natCast_dvd]
  exact Int.Prime.dvd_pow hp h

theorem prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ} (hp : Nat.Prime p)
    (h : (p : ℤ) ∣ 2 * m ^ 2) : p = 2 ∨ p ∣ Int.natAbs m := by
  cases' Int.Prime.dvd_mul hp h with hp2 hpp
  · apply Or.intro_left
    exact le_antisymm (Nat.le_of_dvd zero_lt_two hp2) (Nat.Prime.two_le hp)
  · apply Or.intro_right
    rw [sq, Int.natAbs_mul] at hpp
    exact or_self_iff.mp ((Nat.Prime.dvd_mul hp).mp hpp)

theorem Int.exists_prime_and_dvd {n : ℤ} (hn : n.natAbs ≠ 1) : ∃ p, Prime p ∧ p ∣ n := by
  obtain ⟨p, pp, pd⟩ := Nat.exists_prime_and_dvd hn
  exact ⟨p, Nat.prime_iff_prime_int.mp pp, Int.natCast_dvd.mpr pd⟩


theorem Int.prime_iff_natAbs_prime {k : ℤ} : Prime k ↔ Nat.Prime k.natAbs :=
  (Int.associated_natAbs k).prime_iff.trans Nat.prime_iff_prime_int.symm

namespace Int

theorem zmultiples_natAbs (a : ℤ) :
    AddSubgroup.zmultiples (a.natAbs : ℤ) = AddSubgroup.zmultiples a :=
  le_antisymm (AddSubgroup.zmultiples_le_of_mem (mem_zmultiples_iff.mpr (dvd_natAbs.mpr dvd_rfl)))
    (AddSubgroup.zmultiples_le_of_mem (mem_zmultiples_iff.mpr (natAbs_dvd.mpr dvd_rfl)))

theorem span_natAbs (a : ℤ) : Ideal.span ({(a.natAbs : ℤ)} : Set ℤ) = Ideal.span {a} := by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact (associated_natAbs _).symm

theorem eq_pow_of_mul_eq_pow_odd_left {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ} (hk : Odd k)
    (h : a * b = c ^ k) : ∃ d, a = d ^ k := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  replace hd := hd.symm
  rw [associated_iff_natAbs, natAbs_eq_natAbs_iff, ← hk.neg_pow] at hd
  obtain rfl | rfl := hd <;> exact ⟨_, rfl⟩

@[deprecated (since := "2024-07-12")]
alias eq_pow_of_mul_eq_pow_bit1_left := eq_pow_of_mul_eq_pow_odd_left

theorem eq_pow_of_mul_eq_pow_odd_right {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ} (hk : Odd k)
    (h : a * b = c ^ k) : ∃ d, b = d ^ k :=
  eq_pow_of_mul_eq_pow_odd_left hab.symm hk (by rwa [mul_comm] at h)

@[deprecated (since := "2024-07-12")]
alias eq_pow_of_mul_eq_pow_bit1_right := eq_pow_of_mul_eq_pow_odd_right

theorem eq_pow_of_mul_eq_pow_odd {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ} (hk : Odd k)
    (h : a * b = c ^ k) : (∃ d, a = d ^ k) ∧ ∃ e, b = e ^ k :=
  ⟨eq_pow_of_mul_eq_pow_odd_left hab hk h, eq_pow_of_mul_eq_pow_odd_right hab hk h⟩

@[deprecated (since := "2024-07-12")] alias eq_pow_of_mul_eq_pow_bit1 := eq_pow_of_mul_eq_pow_odd

end Int
