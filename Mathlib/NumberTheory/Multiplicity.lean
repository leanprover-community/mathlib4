/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen, Mantas Bakšys
-/
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
# Multiplicity in Number Theory

This file contains results in number theory relating to multiplicity.

## Main statements

* `multiplicity.Int.pow_sub_pow` is the lifting the exponent lemma for odd primes.
  We also prove several variations of the lemma.

## References

* [Wikipedia, *Lifting-the-exponent lemma*]
  (https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma)
-/


open Ideal Ideal.Quotient Finset

variable {R : Type*} {n : ℕ}

section CommRing

variable [CommRing R] {a b x y : R}

theorem dvd_geom_sum₂_iff_of_dvd_sub {x y p : R} (h : p ∣ x - y) :
    (p ∣ ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) ↔ p ∣ n * y ^ (n - 1) := by
  rw [← mem_span_singleton, ← Ideal.Quotient.eq] at h
  simp only [← mem_span_singleton, ← eq_zero_iff_mem, RingHom.map_geom_sum₂, h, geom_sum₂_self,
    map_mul, map_pow, map_natCast]

theorem dvd_geom_sum₂_iff_of_dvd_sub' {x y p : R} (h : p ∣ x - y) :
    (p ∣ ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) ↔ p ∣ n * x ^ (n - 1) := by
  rw [geom_sum₂_comm, dvd_geom_sum₂_iff_of_dvd_sub]; simpa using h.neg_right

theorem dvd_geom_sum₂_self {x y : R} (h : ↑n ∣ x - y) :
    ↑n ∣ ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) :=
  (dvd_geom_sum₂_iff_of_dvd_sub h).mpr (dvd_mul_right _ _)

theorem sq_dvd_add_pow_sub_sub (p x : R) (n : ℕ) :
    p ^ 2 ∣ (x + p) ^ n - x ^ (n - 1) * p * n - x ^ n := by
  rcases n with - | n
  · simp only [pow_zero, Nat.cast_zero, sub_zero, sub_self, dvd_zero, mul_zero]
  · simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.cast_succ, add_pow, Finset.sum_range_succ,
      Nat.choose_self, tsub_self, pow_one, Nat.choose_succ_self_right, pow_zero,
      mul_one, Nat.cast_zero, zero_add, add_tsub_cancel_left]
    suffices p ^ 2 ∣ ∑ i ∈ range n, x ^ i * p ^ (n + 1 - i) * ↑((n + 1).choose i) by
      convert this; abel
    apply Finset.dvd_sum
    intro y hy
    calc
      p ^ 2 ∣ p ^ (n + 1 - y) :=
        pow_dvd_pow p (le_tsub_of_add_le_left (by linarith [Finset.mem_range.mp hy]))
      _ ∣ x ^ y * p ^ (n + 1 - y) * ↑((n + 1).choose y) :=
        dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem not_dvd_geom_sum₂ {p : R} (hp : Prime p) (hxy : p ∣ x - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n) :
    ¬p ∣ ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := fun h =>
  hx <|
    hp.dvd_of_dvd_pow <| (hp.dvd_or_dvd <| (dvd_geom_sum₂_iff_of_dvd_sub' hxy).mp h).resolve_left hn

variable {p : ℕ} (a b)

theorem odd_sq_dvd_geom_sum₂_sub (hp : Odd p) :
    (p : R) ^ 2 ∣ (∑ i ∈ range p, (a + p * b) ^ i * a ^ (p - 1 - i)) - p * a ^ (p - 1) := by
  have h1 : ∀ (i : ℕ),
      (p : R) ^ 2 ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * i + a ^ i) := by
    intro i
    calc
      ↑p ^ 2 ∣ (↑p * b) ^ 2 := by simp only [mul_pow, dvd_mul_right]
      _ ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) := by
        simp only [sq_dvd_add_pow_sub_sub (↑p * b) a i, ← sub_sub]
  simp_rw [← mem_span_singleton, ← Ideal.Quotient.eq] at *
  let s : R := (p : R)^2
  calc
    (Ideal.Quotient.mk (span {s})) (∑ i ∈ range p, (a + (p : R) * b) ^ i * a ^ (p - 1 - i)) =
        ∑ i ∈ Finset.range p,
        mk (span {s}) ((a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) * a ^ (p - 1 - i)) := by
      simp_rw [s, RingHom.map_geom_sum₂, ← map_pow, h1, ← map_mul]
    _ =
        mk (span {s})
            (∑ x ∈ Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (∑ x ∈ Finset.range p, a ^ (x + (p - 1 - x))) := by
      ring_nf
      simp_rw [← map_sum, sum_add_distrib, map_add]
    _ =
        mk (span {s})
            (∑ x ∈ Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (∑ _x ∈ Finset.range p, a ^ (p - 1)) := by
      rw [add_right_inj]
      have : ∀ (x : ℕ), (hx : x ∈ range p) → a ^ (x + (p - 1 - x)) = a ^ (p - 1) := by
        intro x hx
        rw [← Nat.add_sub_assoc _ x, Nat.add_sub_cancel_left]
        exact Nat.le_sub_one_of_lt (Finset.mem_range.mp hx)
      rw [Finset.sum_congr rfl this]
    _ =
        mk (span {s})
            (∑ x ∈ Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (↑p * a ^ (p - 1)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ =
        mk (span {s}) (↑p * b * ∑ x ∈ Finset.range p, a ^ (p - 2) * x) +
          mk (span {s}) (↑p * a ^ (p - 1)) := by
      simp only [Finset.mul_sum, ← mul_assoc, ← pow_add]
      rw [Finset.sum_congr rfl]
      rintro (⟨⟩ | ⟨x⟩) hx
      · rw [Nat.cast_zero, mul_zero, mul_zero]
      · have : x.succ - 1 + (p - 1 - x.succ) = p - 2 := by
          rw [← Nat.add_sub_assoc (Nat.le_sub_one_of_lt (Finset.mem_range.mp hx))]
          exact congr_arg Nat.pred (Nat.add_sub_cancel_left _ _)
        rw [this]
        ring1
    _ = mk (span {s}) (↑p * a ^ (p - 1)) := by
      have : Finset.sum (range p) (fun (x : ℕ) ↦ (x : R)) =
          ((Finset.sum (range p) (fun (x : ℕ) ↦ (x : ℕ)))) := by simp only [Nat.cast_sum]
      simp only [add_eq_right, ← Finset.mul_sum, this]
      norm_cast
      simp only [Finset.sum_range_id]
      norm_cast
      simp only [Nat.cast_mul, map_mul,
          Nat.mul_div_assoc p (even_iff_two_dvd.mp (Nat.Odd.sub_odd hp odd_one))]
      ring_nf
      rw [mul_assoc, mul_assoc]
      refine mul_eq_zero_of_left ?_ _
      refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
      simp [s, mem_span_singleton]

section IntegralDomain

variable [IsDomain R]

theorem emultiplicity_pow_sub_pow_of_prime {p : R} (hp : Prime p) {x y : R}
    (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : ¬p ∣ n) :
    emultiplicity p (x ^ n - y ^ n) = emultiplicity p (x - y) := by
  rw [← geom_sum₂_mul, emultiplicity_mul hp,
    emultiplicity_eq_zero.2 (not_dvd_geom_sum₂ hp hxy hx hn), zero_add]

variable (hp : Prime (p : R)) (hp1 : Odd p) (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x)
include hp hp1 hxy hx

theorem emultiplicity_geom_sum₂_eq_one :
    emultiplicity (↑p) (∑ i ∈ range p, x ^ i * y ^ (p - 1 - i)) = 1 := by
  rw [← Nat.cast_one]
  refine emultiplicity_eq_coe.2 ⟨?_, ?_⟩
  · rw [pow_one]
    exact dvd_geom_sum₂_self hxy
  rw [dvd_iff_dvd_of_dvd_sub hxy] at hx
  obtain ⟨k, hk⟩ := hxy
  rw [one_add_one_eq_two, eq_add_of_sub_eq' hk]
  refine mt (dvd_iff_dvd_of_dvd_sub (@odd_sq_dvd_geom_sum₂_sub _ _ y k _ hp1)).mp ?_
  rw [pow_two, mul_dvd_mul_iff_left hp.ne_zero]
  exact mt hp.dvd_of_dvd_pow hx

theorem emultiplicity_pow_prime_sub_pow_prime :
    emultiplicity (↑p) (x ^ p - y ^ p) = emultiplicity (↑p) (x - y) + 1 := by
  rw [← geom_sum₂_mul, emultiplicity_mul hp, emultiplicity_geom_sum₂_eq_one hp hp1 hxy hx, add_comm]

theorem emultiplicity_pow_prime_pow_sub_pow_prime_pow (a : ℕ) :
    emultiplicity (↑p) (x ^ p ^ a - y ^ p ^ a) = emultiplicity (↑p) (x - y) + a := by
  induction a with
  | zero => rw [Nat.cast_zero, add_zero, pow_zero, pow_one, pow_one]
  | succ a h_ind =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← h_ind, pow_succ, pow_mul, pow_mul]
    apply emultiplicity_pow_prime_sub_pow_prime hp hp1
    · rw [← geom_sum₂_mul]
      exact dvd_mul_of_dvd_right hxy _
    · exact fun h => hx (hp.dvd_of_dvd_pow h)

end IntegralDomain

section LiftingTheExponent

variable (hp : Nat.Prime p) (hp1 : Odd p)
include hp hp1

/-- **Lifting the exponent lemma** for odd primes. -/
theorem Int.emultiplicity_pow_sub_pow {x y : ℤ} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : ℕ) :
    emultiplicity (↑p) (x ^ n - y ^ n) = emultiplicity (↑p) (x - y) + emultiplicity p n := by
  rcases n with - | n
  · simp only [emultiplicity_zero, add_top, pow_zero, sub_self]
  have h : FiniteMultiplicity _ _ := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, n.succ_pos⟩
  simp only [Nat.succ_eq_add_one] at h
  rcases emultiplicity_eq_coe.mp h.emultiplicity_eq_multiplicity with ⟨⟨k, hk⟩, hpn⟩
  conv_lhs => rw [hk, pow_mul, pow_mul]
  rw [Nat.prime_iff_prime_int] at hp
  rw [emultiplicity_pow_sub_pow_of_prime hp,
    emultiplicity_pow_prime_pow_sub_pow_prime_pow hp hp1 hxy hx, h.emultiplicity_eq_multiplicity]
  · rw [← geom_sum₂_mul]
    exact dvd_mul_of_dvd_right hxy _
  · exact fun h => hx (hp.dvd_of_dvd_pow h)
  · rw [Int.natCast_dvd_natCast]
    rintro ⟨c, rfl⟩
    refine hpn ⟨c, ?_⟩
    rwa [pow_succ, mul_assoc]

theorem Int.emultiplicity_pow_add_pow {x y : ℤ} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x)
    {n : ℕ} (hn : Odd n) :
    emultiplicity (↑p) (x ^ n + y ^ n) = emultiplicity (↑p) (x + y) + emultiplicity p n := by
  rw [← sub_neg_eq_add] at hxy
  rw [← sub_neg_eq_add, ← sub_neg_eq_add, ← Odd.neg_pow hn]
  exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n

theorem Nat.emultiplicity_pow_sub_pow {x y : ℕ} (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : ℕ) :
    emultiplicity p (x ^ n - y ^ n) = emultiplicity p (x - y) + emultiplicity p n := by
  obtain hyx | hyx := le_total y x
  · iterate 2 rw [← Int.natCast_emultiplicity]
    rw [Int.ofNat_sub (Nat.pow_le_pow_left hyx n)]
    rw [← Int.natCast_dvd_natCast] at hxy hx
    rw [Int.natCast_sub hyx] at *
    push_cast at *
    exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n
  · simp only [Nat.sub_eq_zero_iff_le.mpr (Nat.pow_le_pow_left hyx n), emultiplicity_zero,
    Nat.sub_eq_zero_iff_le.mpr hyx, top_add]

theorem Nat.emultiplicity_pow_add_pow {x y : ℕ} (hxy : p ∣ x + y) (hx : ¬p ∣ x)
    {n : ℕ} (hn : Odd n) :
    emultiplicity p (x ^ n + y ^ n) = emultiplicity p (x + y) + emultiplicity p n := by
  iterate 2 rw [← Int.natCast_emultiplicity]
  rw [← Int.natCast_dvd_natCast] at hxy hx
  push_cast at *
  exact Int.emultiplicity_pow_add_pow hp hp1 hxy hx hn

end LiftingTheExponent

end CommRing

theorem pow_two_pow_sub_pow_two_pow [CommRing R] {x y : R} (n : ℕ) :
    x ^ 2 ^ n - y ^ 2 ^ n = (∏ i ∈ Finset.range n, (x ^ 2 ^ i + y ^ 2 ^ i)) * (x - y) := by
  induction n with
  | zero => simp only [pow_zero, pow_one, range_zero, prod_empty, one_mul]
  | succ d hd =>
    suffices x ^ 2 ^ d.succ - y ^ 2 ^ d.succ = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d) by
      rw [this, hd, Finset.prod_range_succ, ← mul_assoc, mul_comm (x ^ 2 ^ d + y ^ 2 ^ d)]
    rw [Nat.succ_eq_add_one]
    ring

theorem Int.sq_mod_four_eq_one_of_odd {x : ℤ} : Odd x → x ^ 2 % 4 = 1 := by
  intro hx
  unfold Odd at hx
  rcases hx with ⟨_, rfl⟩
  ring_nf
  rw [add_assoc, ← add_mul, Int.add_mul_emod_self_right]
  decide

lemma Int.eight_dvd_sq_sub_one_of_odd {k : ℤ} (hk : Odd k) : 8 ∣ k ^ 2 - 1 := by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by ring
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)

lemma Nat.eight_dvd_sq_sub_one_of_odd {k : ℕ} (hk : Odd k) : 8 ∣ k ^ 2 - 1 := by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by ring_nf; grind
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)

theorem Int.two_pow_two_pow_add_two_pow_two_pow {x y : ℤ} (hx : ¬2 ∣ x) (hxy : 4 ∣ x - y) (i : ℕ) :
    emultiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑(1 : ℕ) := by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  refine emultiplicity_eq_coe.mpr ⟨?_, ?_⟩
  · rw [pow_one, ← even_iff_two_dvd]
    exact hx_odd.pow.add_odd hy_odd.pow
  rcases i with - | i
  · grind
  suffices ∀ x : ℤ, Odd x → x ^ 2 ^ (i + 1) % 4 = 1 by
    rw [show (2 ^ (1 + 1) : ℤ) = 4 by simp, Int.dvd_iff_emod_eq_zero, Int.add_emod,
      this _ hx_odd, this _ hy_odd]
    decide
  intro x hx
  rw [pow_succ', mul_comm, pow_mul, Int.sq_mod_four_eq_one_of_odd hx.pow]

theorem Int.two_pow_two_pow_sub_pow_two_pow {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x) :
    emultiplicity 2 (x ^ 2 ^ n - y ^ 2 ^ n) = emultiplicity 2 (x - y) + n := by
  simp only [pow_two_pow_sub_pow_two_pow n, emultiplicity_mul Int.prime_two,
    Finset.emultiplicity_prod Int.prime_two, add_comm, Nat.cast_one, Finset.sum_const,
    Finset.card_range, nsmul_one, Int.two_pow_two_pow_add_two_pow_two_pow hx hxy]

theorem Int.two_pow_sub_pow' {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x) :
    emultiplicity 2 (x ^ n - y ^ n) = emultiplicity 2 (x - y) + emultiplicity (2 : ℤ) n := by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  rcases n with - | n
  · simp only [pow_zero, sub_self, emultiplicity_zero, Int.ofNat_zero, add_top]
  have h : FiniteMultiplicity 2 n.succ := Nat.finiteMultiplicity_iff.mpr ⟨by simp, n.succ_pos⟩
  simp only [Nat.succ_eq_add_one] at h
  rcases emultiplicity_eq_coe.mp h.emultiplicity_eq_multiplicity with ⟨⟨k, hk⟩, hpn⟩
  rw [hk, pow_mul, pow_mul, emultiplicity_pow_sub_pow_of_prime,
    Int.two_pow_two_pow_sub_pow_two_pow _ hxy hx, ← hk]
  · norm_cast
    rw [h.emultiplicity_eq_multiplicity]
  · exact Int.prime_two
  · simpa only [even_iff_two_dvd] using hx_odd.pow.sub_odd hy_odd.pow
  · simpa only [even_iff_two_dvd, ← Int.not_even_iff_odd] using hx_odd.pow
  norm_cast
  contrapose! hpn
  rw [pow_succ]
  conv_rhs => rw [hk]
  exact mul_dvd_mul_left _ hpn

/-- **Lifting the exponent lemma** for `p = 2` -/
theorem Int.two_pow_sub_pow {x y : ℤ} {n : ℕ} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) (hn : Even n) :
    emultiplicity 2 (x ^ n - y ^ n) + 1 =
      emultiplicity 2 (x + y) + emultiplicity 2 (x - y) + emultiplicity (2 : ℤ) n := by
  have hy : Odd y := by
    rw [← even_iff_two_dvd, Int.not_even_iff_odd] at hx
    replace hxy := (@even_neg _ _ (x - y)).mpr (even_iff_two_dvd.mpr hxy)
    convert Even.add_odd hxy hx
    abel
  obtain ⟨d, hd⟩ := hn
  subst hd
  simp only [← two_mul, pow_mul]
  have hxy4 : 4 ∣ x ^ 2 - y ^ 2 := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, Int.sq_mod_four_eq_one_of_odd _,
      Int.sq_mod_four_eq_one_of_odd hy]
    · simp
    · simp only [← Int.not_even_iff_odd, even_iff_two_dvd, hx, not_false_iff]
  rw [Int.two_pow_sub_pow' d hxy4 _, sq_sub_sq, ← Int.ofNat_mul_out,
    emultiplicity_mul Int.prime_two, emultiplicity_mul Int.prime_two]
  · suffices emultiplicity (2 : ℤ) ↑(2 : ℕ) = 1 by rw [this, add_comm 1, ← add_assoc]
    norm_cast
    rw [FiniteMultiplicity.emultiplicity_self]
    rw [Nat.finiteMultiplicity_iff]
    decide
  · rw [← even_iff_two_dvd, Int.not_even_iff_odd]
    apply Odd.pow
    simp only [← Int.not_even_iff_odd, even_iff_two_dvd, hx, not_false_iff]

theorem Nat.two_pow_sub_pow {x y : ℕ} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : ℕ} (hn : Even n) :
    emultiplicity 2 (x ^ n - y ^ n) + 1 =
      emultiplicity 2 (x + y) + emultiplicity 2 (x - y) + emultiplicity 2 n := by
  obtain hyx | hyx := le_total y x
  · iterate 3 rw [← Int.natCast_emultiplicity]
    simp only [Int.ofNat_sub hyx, Int.ofNat_sub (pow_le_pow_left' hyx _), Int.natCast_add,
      Int.natCast_pow]
    rw [← Int.natCast_dvd_natCast] at hx
    rw [← Int.natCast_dvd_natCast, Int.ofNat_sub hyx] at hxy
    convert Int.two_pow_sub_pow hxy hx hn using 2
    rw [← Int.natCast_emultiplicity]
    rfl
  · simp only [Nat.sub_eq_zero_iff_le.mpr hyx,
      Nat.sub_eq_zero_iff_le.mpr (pow_le_pow_left' hyx n), emultiplicity_zero,
      top_add, add_top]

namespace padicValNat

variable {x y : ℕ}

theorem pow_two_sub_pow (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : ℕ} (hn : n ≠ 0)
    (hneven : Even n) :
    padicValNat 2 (x ^ n - y ^ n) + 1 =
      padicValNat 2 (x + y) + padicValNat 2 (x - y) + padicValNat 2 n := by
  simp only [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
  iterate 4 rw [padicValNat_eq_emultiplicity]
  · exact Nat.two_pow_sub_pow hxy hx hneven
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · omega
  · simp [← Nat.pos_iff_ne_zero, tsub_pos_iff_lt, Nat.pow_lt_pow_left hyx hn]

variable {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p)
include hp hp1

theorem pow_sub_pow (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : n ≠ 0) :
    padicValNat p (x ^ n - y ^ n) = padicValNat p (x - y) + padicValNat p n := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_sub_pow hp.out hp1 hxy hx n
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hyx hn)

theorem pow_add_pow (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : ℕ} (hn : Odd n) :
    padicValNat p (x ^ n + y ^ n) = padicValNat p (x + y) + padicValNat p n := by
  rcases y with - | y
  · contradiction
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_add_pow hp.out hp1 hxy hx hn
  · exact (Odd.pos hn).ne'
  · simp only [← Nat.pos_iff_ne_zero, add_pos_iff, Nat.succ_pos', or_true]
  · exact (Nat.lt_add_left _ (pow_pos y.succ_pos _)).ne'

end padicValNat
