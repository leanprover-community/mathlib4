/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

#align_import ring_theory.int.basic from "leanprover-community/mathlib"@"e655e4ea5c6d02854696f97494997ba4c31be802"

/-!
# Divisibility over ℕ and ℤ

This file collects results for the integers and natural numbers that use abstract algebra in
their proofs or cases of ℕ and ℤ being examples of structures in abstract algebra.

## Main statements

* `Nat.factors_eq`: the multiset of elements of `Nat.factors` is equal to the factors
   given by the `UniqueFactorizationMonoid` instance
* ℤ is a `NormalizationMonoid`
* ℤ is a `GCDMonoid`

## Tags

prime, irreducible, natural numbers, integers, normalization monoid, gcd monoid,
greatest common divisor, prime factorization, prime factors, unique factorization,
unique factors
-/

namespace Int

section NormalizationMonoid

instance normalizationMonoid : NormalizationMonoid ℤ where
  normUnit a := if 0 ≤ a then 1 else -1
  normUnit_zero := if_pos le_rfl
  normUnit_mul {a b} hna hnb := by
    cases' hna.lt_or_lt with ha ha <;> cases' hnb.lt_or_lt with hb hb <;>
      simp [mul_nonneg_iff, ha.le, ha.not_le, hb.le, hb.not_le]
  normUnit_coe_units u :=
    (units_eq_one_or u).elim (fun eq => eq.symm ▸ if_pos zero_le_one) fun eq =>
      eq.symm ▸ if_neg (not_le_of_gt <| show (-1 : ℤ) < 0 by decide)

-- Porting note: added
theorem normUnit_eq (z : ℤ) : normUnit z = if 0 ≤ z then 1 else -1 := rfl

theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z := by
  rw [normalize_apply, normUnit_eq, if_pos h, Units.val_one, mul_one]
#align int.normalize_of_nonneg Int.normalize_of_nonneg

theorem normalize_of_nonpos {z : ℤ} (h : z ≤ 0) : normalize z = -z := by
  obtain rfl | h := h.eq_or_lt
  · simp
  · rw [normalize_apply, normUnit_eq, if_neg (not_le_of_gt h), Units.val_neg, Units.val_one,
      mul_neg_one]
#align int.normalize_of_nonpos Int.normalize_of_nonpos

theorem normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
  normalize_of_nonneg (ofNat_le_ofNat_of_le <| Nat.zero_le n)
#align int.normalize_coe_nat Int.normalize_coe_nat

theorem abs_eq_normalize (z : ℤ) : |z| = normalize z := by
  cases le_total 0 z <;> simp [-normalize_apply, normalize_of_nonneg, normalize_of_nonpos, *]
#align int.abs_eq_normalize Int.abs_eq_normalize

theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z :=
  abs_eq_self.1 <| by rw [abs_eq_normalize, hz]
#align int.nonneg_of_normalize_eq_self Int.nonneg_of_normalize_eq_self

theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z :=
  ⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩
#align int.nonneg_iff_normalize_eq_self Int.nonneg_iff_normalize_eq_self

theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b :=
  dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.dvd h.symm.dvd
#align int.eq_of_associated_of_nonneg Int.eq_of_associated_of_nonneg

end NormalizationMonoid

section GCDMonoid

instance : GCDMonoid ℤ where
  gcd a b := Int.gcd a b
  lcm a b := Int.lcm a b
  gcd_dvd_left a b := Int.gcd_dvd_left
  gcd_dvd_right a b := Int.gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by
    rw [← Int.ofNat_mul, gcd_mul_lcm, natCast_natAbs, abs_eq_normalize]
    exact normalize_associated (a * b)
  lcm_zero_left a := natCast_eq_zero.2 <| Nat.lcm_zero_left _
  lcm_zero_right a := natCast_eq_zero.2 <| Nat.lcm_zero_right _

instance : NormalizedGCDMonoid ℤ :=
  { Int.normalizationMonoid,
    (inferInstance : GCDMonoid ℤ) with
    normalize_gcd := fun _ _ => normalize_coe_nat _
    normalize_lcm := fun _ _ => normalize_coe_nat _ }

theorem coe_gcd (i j : ℤ) : ↑(Int.gcd i j) = GCDMonoid.gcd i j :=
  rfl
#align int.coe_gcd Int.coe_gcd

theorem coe_lcm (i j : ℤ) : ↑(Int.lcm i j) = GCDMonoid.lcm i j :=
  rfl
#align int.coe_lcm Int.coe_lcm

theorem natAbs_gcd (i j : ℤ) : natAbs (GCDMonoid.gcd i j) = Int.gcd i j :=
  rfl
#align int.nat_abs_gcd Int.natAbs_gcd

theorem natAbs_lcm (i j : ℤ) : natAbs (GCDMonoid.lcm i j) = Int.lcm i j :=
  rfl
#align int.nat_abs_lcm Int.natAbs_lcm

end GCDMonoid

theorem exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ) (_ : IsUnit u), (Int.natAbs a : ℤ) = u * a := by
  cases' natAbs_eq a with h h
  · use 1, isUnit_one
    rw [← h, one_mul]
  · use -1, isUnit_one.neg
    rw [← neg_eq_iff_eq_neg.mpr h]
    simp only [neg_mul, one_mul]
#align int.exists_unit_of_abs Int.exists_unit_of_abs

theorem gcd_eq_natAbs {a b : ℤ} : Int.gcd a b = Nat.gcd a.natAbs b.natAbs :=
  rfl
#align int.gcd_eq_nat_abs Int.gcd_eq_natAbs

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
#align int.gcd_eq_one_iff_coprime Int.gcd_eq_one_iff_coprime

theorem coprime_iff_nat_coprime {a b : ℤ} : IsCoprime a b ↔ Nat.Coprime a.natAbs b.natAbs := by
  rw [← gcd_eq_one_iff_coprime, Nat.coprime_iff_gcd_eq_one, gcd_eq_natAbs]
#align int.coprime_iff_nat_coprime Int.coprime_iff_nat_coprime

/-- If `gcd a (m * n) ≠ 1`, then `gcd a m ≠ 1` or `gcd a n ≠ 1`. -/
theorem gcd_ne_one_iff_gcd_mul_right_ne_one {a : ℤ} {m n : ℕ} :
    a.gcd (m * n) ≠ 1 ↔ a.gcd m ≠ 1 ∨ a.gcd n ≠ 1 := by
  simp only [gcd_eq_one_iff_coprime, ← not_and_or, not_iff_not, IsCoprime.mul_right_iff]
#align int.gcd_ne_one_iff_gcd_mul_right_ne_one Int.gcd_ne_one_iff_gcd_mul_right_ne_one

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
#align int.sq_of_gcd_eq_one Int.sq_of_gcd_eq_one

theorem sq_of_coprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 2) :
    ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2 :=
  sq_of_gcd_eq_one (gcd_eq_one_iff_coprime.mpr h) heq
#align int.sq_of_coprime Int.sq_of_coprime

theorem natAbs_euclideanDomain_gcd (a b : ℤ) :
    Int.natAbs (EuclideanDomain.gcd a b) = Int.gcd a b := by
  apply Nat.dvd_antisymm <;> rw [← Int.natCast_dvd_natCast]
  · rw [Int.natAbs_dvd]
    exact Int.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
  · rw [Int.dvd_natAbs]
    exact EuclideanDomain.dvd_gcd Int.gcd_dvd_left Int.gcd_dvd_right
#align int.nat_abs_euclidean_domain_gcd Int.natAbs_euclideanDomain_gcd

end Int

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associatesIntEquivNat : Associates ℤ ≃ ℕ := by
  refine ⟨(·.out.natAbs), (Associates.mk ·), ?_, fun n ↦ ?_⟩
  · refine Associates.forall_associated.2 fun a ↦ ?_
    refine Associates.mk_eq_mk_iff_associated.2 <| Associated.symm <| ⟨normUnit a, ?_⟩
    simp [Int.abs_eq_normalize]
  · dsimp only [Associates.out_mk]
    rw [← Int.abs_eq_normalize, Int.natAbs_abs, Int.natAbs_ofNat]
#align associates_int_equiv_nat associatesIntEquivNat

theorem Int.Prime.dvd_mul {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) :
    p ∣ m.natAbs ∨ p ∣ n.natAbs := by
  rwa [← hp.dvd_mul, ← Int.natAbs_mul, ← Int.natCast_dvd]
#align int.prime.dvd_mul Int.Prime.dvd_mul

theorem Int.Prime.dvd_mul' {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) :
    (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n := by
  rw [Int.natCast_dvd, Int.natCast_dvd]
  exact Int.Prime.dvd_mul hp h
#align int.prime.dvd_mul' Int.Prime.dvd_mul'

theorem Int.Prime.dvd_pow {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ k) :
    p ∣ n.natAbs := by
  rw [Int.natCast_dvd, Int.natAbs_pow] at h
  exact hp.dvd_of_dvd_pow h
#align int.prime.dvd_pow Int.Prime.dvd_pow

theorem Int.Prime.dvd_pow' {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ k) :
    (p : ℤ) ∣ n := by
  rw [Int.natCast_dvd]
  exact Int.Prime.dvd_pow hp h
#align int.prime.dvd_pow' Int.Prime.dvd_pow'

theorem prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ} (hp : Nat.Prime p)
    (h : (p : ℤ) ∣ 2 * m ^ 2) : p = 2 ∨ p ∣ Int.natAbs m := by
  cases' Int.Prime.dvd_mul hp h with hp2 hpp
  · apply Or.intro_left
    exact le_antisymm (Nat.le_of_dvd zero_lt_two hp2) (Nat.Prime.two_le hp)
  · apply Or.intro_right
    rw [sq, Int.natAbs_mul] at hpp
    exact or_self_iff.mp ((Nat.Prime.dvd_mul hp).mp hpp)
#align prime_two_or_dvd_of_dvd_two_mul_pow_self_two prime_two_or_dvd_of_dvd_two_mul_pow_self_two

theorem Int.exists_prime_and_dvd {n : ℤ} (hn : n.natAbs ≠ 1) : ∃ p, Prime p ∧ p ∣ n := by
  obtain ⟨p, pp, pd⟩ := Nat.exists_prime_and_dvd hn
  exact ⟨p, Nat.prime_iff_prime_int.mp pp, Int.natCast_dvd.mpr pd⟩
#align int.exists_prime_and_dvd Int.exists_prime_and_dvd


theorem Int.associated_natAbs (k : ℤ) : Associated k k.natAbs :=
  associated_of_dvd_dvd (Int.dvd_natCast.mpr dvd_rfl) (Int.natAbs_dvd.mpr dvd_rfl)
#align int.associated_nat_abs Int.associated_natAbs

theorem Int.prime_iff_natAbs_prime {k : ℤ} : Prime k ↔ Nat.Prime k.natAbs :=
  (Int.associated_natAbs k).prime_iff.trans Nat.prime_iff_prime_int.symm
#align int.prime_iff_nat_abs_prime Int.prime_iff_natAbs_prime

theorem Int.associated_iff_natAbs {a b : ℤ} : Associated a b ↔ a.natAbs = b.natAbs := by
  rw [← dvd_dvd_iff_associated, ← Int.natAbs_dvd_natAbs, ← Int.natAbs_dvd_natAbs,
    dvd_dvd_iff_associated]
  exact associated_iff_eq
#align int.associated_iff_nat_abs Int.associated_iff_natAbs

theorem Int.associated_iff {a b : ℤ} : Associated a b ↔ a = b ∨ a = -b := by
  rw [Int.associated_iff_natAbs]
  exact Int.natAbs_eq_natAbs_iff
#align int.associated_iff Int.associated_iff

namespace Int

theorem zmultiples_natAbs (a : ℤ) :
    AddSubgroup.zmultiples (a.natAbs : ℤ) = AddSubgroup.zmultiples a :=
  le_antisymm (AddSubgroup.zmultiples_le_of_mem (mem_zmultiples_iff.mpr (dvd_natAbs.mpr dvd_rfl)))
    (AddSubgroup.zmultiples_le_of_mem (mem_zmultiples_iff.mpr (natAbs_dvd.mpr dvd_rfl)))
#align int.zmultiples_nat_abs Int.zmultiples_natAbs

theorem span_natAbs (a : ℤ) : Ideal.span ({(a.natAbs : ℤ)} : Set ℤ) = Ideal.span {a} := by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact (associated_natAbs _).symm
#align int.span_nat_abs Int.span_natAbs

section bit
set_option linter.deprecated false

theorem eq_pow_of_mul_eq_pow_bit1_left {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ bit1 k) : ∃ d, a = d ^ bit1 k := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  replace hd := hd.symm
  rw [associated_iff_natAbs, natAbs_eq_natAbs_iff, ← neg_pow_bit1] at hd
  obtain rfl | rfl := hd <;> exact ⟨_, rfl⟩
#align int.eq_pow_of_mul_eq_pow_bit1_left Int.eq_pow_of_mul_eq_pow_bit1_left

theorem eq_pow_of_mul_eq_pow_bit1_right {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ bit1 k) : ∃ d, b = d ^ bit1 k :=
  eq_pow_of_mul_eq_pow_bit1_left hab.symm (by rwa [mul_comm] at h)
#align int.eq_pow_of_mul_eq_pow_bit1_right Int.eq_pow_of_mul_eq_pow_bit1_right

theorem eq_pow_of_mul_eq_pow_bit1 {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ bit1 k) : (∃ d, a = d ^ bit1 k) ∧ ∃ e, b = e ^ bit1 k :=
  ⟨eq_pow_of_mul_eq_pow_bit1_left hab h, eq_pow_of_mul_eq_pow_bit1_right hab h⟩
#align int.eq_pow_of_mul_eq_pow_bit1 Int.eq_pow_of_mul_eq_pow_bit1

end bit

end Int
