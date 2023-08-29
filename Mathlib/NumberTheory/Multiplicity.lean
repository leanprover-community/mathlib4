/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen, Mantas Bakšys
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Int.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Init.Meta.WellFoundedTactics

#align_import number_theory.multiplicity from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

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

open BigOperators

variable {R : Type*} {n : ℕ}

section CommRing

variable [CommRing R] {a b x y : R}

theorem dvd_geom_sum₂_iff_of_dvd_sub {x y p : R} (h : p ∣ x - y) :
    (p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i)) ↔ p ∣ n * y ^ (n - 1) := by
  rw [← mem_span_singleton, ← Ideal.Quotient.eq] at h
  -- ⊢ p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i) ↔ p ∣ ↑n * y ^ (n - 1)
  simp only [← mem_span_singleton, ← eq_zero_iff_mem, RingHom.map_geom_sum₂, h, geom_sum₂_self,
    _root_.map_mul, map_pow, map_natCast]
#align dvd_geom_sum₂_iff_of_dvd_sub dvd_geom_sum₂_iff_of_dvd_sub

theorem dvd_geom_sum₂_iff_of_dvd_sub' {x y p : R} (h : p ∣ x - y) :
    (p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i)) ↔ p ∣ n * x ^ (n - 1) := by
  rw [geom_sum₂_comm, dvd_geom_sum₂_iff_of_dvd_sub]; simpa using h.neg_right
  -- ⊢ p ∣ y - x
                                                     -- 🎉 no goals
#align dvd_geom_sum₂_iff_of_dvd_sub' dvd_geom_sum₂_iff_of_dvd_sub'

theorem dvd_geom_sum₂_self {x y : R} (h : ↑n ∣ x - y) :
    ↑n ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i) :=
  (dvd_geom_sum₂_iff_of_dvd_sub h).mpr (dvd_mul_right _ _)
#align dvd_geom_sum₂_self dvd_geom_sum₂_self

theorem sq_dvd_add_pow_sub_sub (p x : R) (n : ℕ) :
    p ^ 2 ∣ (x + p) ^ n - x ^ (n - 1) * p * n - x ^ n := by
  cases' n with n n
  -- ⊢ p ^ 2 ∣ (x + p) ^ Nat.zero - x ^ (Nat.zero - 1) * p * ↑Nat.zero - x ^ Nat.zero
  · simp only [pow_zero, Nat.cast_zero, sub_zero, sub_self, dvd_zero, Nat.zero_eq, mul_zero]
    -- 🎉 no goals
  · simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.cast_succ, add_pow, Finset.sum_range_succ,
      Nat.choose_self, Nat.succ_sub _, tsub_self, pow_one, Nat.choose_succ_self_right, pow_zero,
      mul_one, Nat.cast_zero, zero_add, Nat.succ_eq_add_one, add_tsub_cancel_left]
    suffices p ^ 2 ∣ ∑ i : ℕ in range n, x ^ i * p ^ (n + 1 - i) * ↑((n + 1).choose i) by
      convert this; abel
    · apply Finset.dvd_sum
      -- ⊢ ∀ (x_1 : ℕ), x_1 ∈ range n → p ^ 2 ∣ x ^ x_1 * p ^ (n + 1 - x_1) * ↑(Nat.cho …
      intro y hy
      -- ⊢ p ^ 2 ∣ x ^ y * p ^ (n + 1 - y) * ↑(Nat.choose (n + 1) y)
      calc
        p ^ 2 ∣ p ^ (n + 1 - y) :=
          pow_dvd_pow p (le_tsub_of_add_le_left (by linarith [Finset.mem_range.mp hy]))
        _ ∣ x ^ y * p ^ (n + 1 - y) * ↑((n + 1).choose y) :=
          dvd_mul_of_dvd_left (dvd_mul_left _ _) _
#align sq_dvd_add_pow_sub_sub sq_dvd_add_pow_sub_sub

theorem not_dvd_geom_sum₂ {p : R} (hp : Prime p) (hxy : p ∣ x - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n) :
    ¬p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i) := fun h =>
  hx <|
    hp.dvd_of_dvd_pow <| (hp.dvd_or_dvd <| (dvd_geom_sum₂_iff_of_dvd_sub' hxy).mp h).resolve_left hn
#align not_dvd_geom_sum₂ not_dvd_geom_sum₂

variable {p : ℕ} (a b)

theorem odd_sq_dvd_geom_sum₂_sub (hp : Odd p) :
    (p : R) ^ 2 ∣ (∑ i in range p, (a + p * b) ^ i * a ^ (p - 1 - i)) - p * a ^ (p - 1) := by
  have h1 : ∀ (i : ℕ),
      (p : R) ^ 2 ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * i + a ^ i) := by
    intro i
    calc
      ↑p ^ 2 ∣ (↑p * b) ^ 2 := by simp only [mul_pow, dvd_mul_right]
      _ ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) := by
        simp only [sq_dvd_add_pow_sub_sub (↑p * b) a i, ← sub_sub]
  simp_rw [← mem_span_singleton, ← Ideal.Quotient.eq] at *
  -- ⊢ ↑(Ideal.Quotient.mk (span {↑p ^ 2})) (∑ i in range p, (a + ↑p * b) ^ i * a ^ …
  let s : R := (p : R)^2
  -- ⊢ ↑(Ideal.Quotient.mk (span {↑p ^ 2})) (∑ i in range p, (a + ↑p * b) ^ i * a ^ …
  calc
    (Ideal.Quotient.mk (span {s})) (∑ i in range p, (a + (p : R) * b) ^ i * a ^ (p - 1 - i)) =
        ∑ i : ℕ in Finset.range p,
        mk (span {s}) ((a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) * a ^ (p - 1 - i)) :=
      by simp_rw [RingHom.map_geom_sum₂, ← map_pow, h1, ← _root_.map_mul]
    _ =
        mk (span {s})
            (∑ x : ℕ in Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (∑ x : ℕ in Finset.range p, a ^ (x + (p - 1 - x))) := by
      ring_nf
      simp only [← pow_add, map_add, Finset.sum_add_distrib, ← map_sum]
      congr
      simp [pow_add a, mul_assoc]
    _ =
        mk (span {s})
            (∑ x : ℕ in Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (∑ x : ℕ in Finset.range p, a ^ (p - 1)) := by
      rw [add_right_inj]
      have : ∀ (x : ℕ), (hx : x ∈ range p) → a ^ (x + (p - 1 - x)) = a ^ (p - 1) := by
        intro x hx
        rw [← Nat.add_sub_assoc _ x, Nat.add_sub_cancel_left]
        exact Nat.le_pred_of_lt (Finset.mem_range.mp hx)
      rw [Finset.sum_congr rfl this]
    _ =
        mk (span {s})
            (∑ x : ℕ in Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (↑p * a ^ (p - 1)) :=
      by simp only [add_right_inj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ =
        mk (span {s}) (↑p * b * ∑ x : ℕ in Finset.range p, a ^ (p - 2) * x) +
          mk (span {s}) (↑p * a ^ (p - 1)) := by
      simp only [Finset.mul_sum, ← mul_assoc, ← pow_add]
      rw [Finset.sum_congr rfl]
      rintro (⟨⟩ | ⟨x⟩) hx
      · rw [Nat.cast_zero, mul_zero, mul_zero]
      · have : x.succ - 1 + (p - 1 - x.succ) = p - 2 := by
          rw [← Nat.add_sub_assoc (Nat.le_pred_of_lt (Finset.mem_range.mp hx))]
          exact congr_arg Nat.pred (Nat.add_sub_cancel_left _ _)
        rw [this]
        ring1
    _ = mk (span {s}) (↑p * a ^ (p - 1)) := by
      have : Finset.sum (range p) (fun (x : ℕ) ↦ (x : R)) =
          ((Finset.sum (range p) (fun (x : ℕ) ↦ (x : ℕ)))) := by simp only [Nat.cast_sum]
      simp only [add_left_eq_self, ← Finset.mul_sum, this]
      norm_cast
      simp only [Finset.sum_range_id]
      norm_cast
      simp only [Nat.cast_mul, _root_.map_mul,
          Nat.mul_div_assoc p (even_iff_two_dvd.mp (Nat.Odd.sub_odd hp odd_one))]
      ring_nf
      rw [mul_assoc, mul_assoc]
      refine' mul_eq_zero_of_left _ _
      refine' Ideal.Quotient.eq_zero_iff_mem.mpr _
      simp [mem_span_singleton]
#align odd_sq_dvd_geom_sum₂_sub odd_sq_dvd_geom_sum₂_sub

namespace multiplicity

section IntegralDomain

variable [IsDomain R] [@DecidableRel R (· ∣ ·)]

theorem pow_sub_pow_of_prime {p : R} (hp : Prime p) {x y : R} (hxy : p ∣ x - y) (hx : ¬p ∣ x)
    {n : ℕ} (hn : ¬p ∣ n) : multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) := by
  rw [← geom_sum₂_mul, multiplicity.mul hp, multiplicity_eq_zero.2 (not_dvd_geom_sum₂ hp hxy hx hn),
    zero_add]
#align multiplicity.pow_sub_pow_of_prime multiplicity.pow_sub_pow_of_prime

variable (hp : Prime (p : R)) (hp1 : Odd p) (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x)

theorem geom_sum₂_eq_one : multiplicity (↑p) (∑ i in range p, x ^ i * y ^ (p - 1 - i)) = 1 := by
  rw [← Nat.cast_one]
  -- ⊢ multiplicity (↑p) (∑ i in range p, x ^ i * y ^ (p - ↑1 - i)) = 1
  refine' multiplicity.eq_coe_iff.2 ⟨_, _⟩
  -- ⊢ ↑p ^ 1 ∣ ∑ i in range p, x ^ i * y ^ (p - ↑1 - i)
  · rw [pow_one]
    -- ⊢ ↑p ∣ ∑ i in range p, x ^ i * y ^ (p - ↑1 - i)
    exact dvd_geom_sum₂_self hxy
    -- 🎉 no goals
  rw [dvd_iff_dvd_of_dvd_sub hxy] at hx
  -- ⊢ ¬↑p ^ (1 + 1) ∣ ∑ i in range p, x ^ i * y ^ (p - ↑1 - i)
  cases' hxy with k hk
  -- ⊢ ¬↑p ^ (1 + 1) ∣ ∑ i in range p, x ^ i * y ^ (p - ↑1 - i)
  rw [one_add_one_eq_two, eq_add_of_sub_eq' hk]
  -- ⊢ ¬↑p ^ 2 ∣ ∑ i in range p, (y + ↑p * k) ^ i * y ^ (p - ↑1 - i)
  refine' mt (dvd_iff_dvd_of_dvd_sub (@odd_sq_dvd_geom_sum₂_sub _ _ y k _ hp1)).mp _
  -- ⊢ ¬↑p ^ 2 ∣ ↑p * y ^ (p - 1)
  rw [pow_two, mul_dvd_mul_iff_left hp.ne_zero]
  -- ⊢ ¬↑p ∣ y ^ (p - 1)
  exact mt hp.dvd_of_dvd_pow hx
  -- 🎉 no goals
#align multiplicity.geom_sum₂_eq_one multiplicity.geom_sum₂_eq_one

theorem pow_prime_sub_pow_prime :
    multiplicity (↑p) (x ^ p - y ^ p) = multiplicity (↑p) (x - y) + 1 := by
  rw [← geom_sum₂_mul, multiplicity.mul hp, geom_sum₂_eq_one hp hp1 hxy hx, add_comm]
  -- 🎉 no goals
#align multiplicity.pow_prime_sub_pow_prime multiplicity.pow_prime_sub_pow_prime

theorem pow_prime_pow_sub_pow_prime_pow (a : ℕ) :
    multiplicity (↑p) (x ^ p ^ a - y ^ p ^ a) = multiplicity (↑p) (x - y) + a := by
  induction' a with a h_ind
  -- ⊢ multiplicity (↑p) (x ^ p ^ Nat.zero - y ^ p ^ Nat.zero) = multiplicity (↑p)  …
  · rw [Nat.cast_zero, add_zero, pow_zero, pow_one, pow_one]
    -- 🎉 no goals
  rw [← Nat.add_one, Nat.cast_add, Nat.cast_one, ← add_assoc, ← h_ind, pow_succ', pow_mul, pow_mul]
  -- ⊢ multiplicity (↑p) ((x ^ p ^ a) ^ p - (y ^ p ^ a) ^ p) = multiplicity (↑p) (x …
  apply pow_prime_sub_pow_prime hp hp1
  -- ⊢ ↑p ∣ x ^ p ^ a - y ^ p ^ a
  · rw [← geom_sum₂_mul]
    -- ⊢ ↑p ∣ (∑ i in range (p ^ a), x ^ i * y ^ (p ^ a - 1 - i)) * (x - y)
    exact dvd_mul_of_dvd_right hxy _
    -- 🎉 no goals
  · exact fun h => hx (hp.dvd_of_dvd_pow h)
    -- 🎉 no goals
#align multiplicity.pow_prime_pow_sub_pow_prime_pow multiplicity.pow_prime_pow_sub_pow_prime_pow

end IntegralDomain

section LiftingTheExponent

variable (hp : Nat.Prime p) (hp1 : Odd p)

/-- **Lifting the exponent lemma** for odd primes. -/
theorem Int.pow_sub_pow {x y : ℤ} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : ℕ) :
    multiplicity (↑p) (x ^ n - y ^ n) = multiplicity (↑p) (x - y) + multiplicity p n := by
  cases' n with n
  -- ⊢ multiplicity (↑p) (x ^ Nat.zero - y ^ Nat.zero) = multiplicity (↑p) (x - y)  …
  · simp only [multiplicity.zero, add_top, pow_zero, sub_self, Nat.zero_eq]
    -- 🎉 no goals
  have h : (multiplicity _ _).Dom := finite_nat_iff.mpr ⟨hp.ne_one, n.succ_pos⟩
  -- ⊢ multiplicity (↑p) (x ^ Nat.succ n - y ^ Nat.succ n) = multiplicity (↑p) (x - …
  rcases eq_coe_iff.mp (PartENat.natCast_get h).symm with ⟨⟨k, hk⟩, hpn⟩
  -- ⊢ multiplicity (↑p) (x ^ Nat.succ n - y ^ Nat.succ n) = multiplicity (↑p) (x - …
  conv_lhs => rw [hk, pow_mul, pow_mul]
  -- ⊢ multiplicity (↑p) ((x ^ p ^ Part.get (multiplicity p (Nat.succ n)) h) ^ k -  …
  rw [Nat.prime_iff_prime_int] at hp
  -- ⊢ multiplicity (↑p) ((x ^ p ^ Part.get (multiplicity p (Nat.succ n)) h) ^ k -  …
  rw [pow_sub_pow_of_prime hp, pow_prime_pow_sub_pow_prime_pow hp hp1 hxy hx, PartENat.natCast_get]
  · rw [← geom_sum₂_mul]
    -- ⊢ ↑p ∣ (∑ i in range (p ^ Part.get (multiplicity p (Nat.succ n)) h), x ^ i * y …
    exact dvd_mul_of_dvd_right hxy _
    -- 🎉 no goals
  · exact fun h => hx (hp.dvd_of_dvd_pow h)
    -- 🎉 no goals
  · rw [Int.coe_nat_dvd]
    -- ⊢ ¬p ∣ k
    rintro ⟨c, rfl⟩
    -- ⊢ False
    refine' hpn ⟨c, _⟩
    -- ⊢ Nat.succ n = p ^ (Part.get (multiplicity p (Nat.succ n)) h + 1) * c
    rwa [pow_succ', mul_assoc]
    -- 🎉 no goals
#align multiplicity.int.pow_sub_pow multiplicity.Int.pow_sub_pow

theorem Int.pow_add_pow {x y : ℤ} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x) {n : ℕ} (hn : Odd n) :
    multiplicity (↑p) (x ^ n + y ^ n) = multiplicity (↑p) (x + y) + multiplicity p n := by
  rw [← sub_neg_eq_add] at hxy
  -- ⊢ multiplicity (↑p) (x ^ n + y ^ n) = multiplicity (↑p) (x + y) + multiplicity …
  rw [← sub_neg_eq_add, ← sub_neg_eq_add, ← Odd.neg_pow hn]
  -- ⊢ multiplicity (↑p) (x ^ n - (-y) ^ n) = multiplicity (↑p) (x - -y) + multipli …
  exact Int.pow_sub_pow hp hp1 hxy hx n
  -- 🎉 no goals
#align multiplicity.int.pow_add_pow multiplicity.Int.pow_add_pow

theorem Nat.pow_sub_pow {x y : ℕ} (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : ℕ) :
    multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) + multiplicity p n := by
  obtain hyx | hyx := le_total y x
  -- ⊢ multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) + multiplicity p n
  · iterate 2 rw [← Int.coe_nat_multiplicity]
    -- ⊢ multiplicity ↑p ↑(x ^ n - y ^ n) = multiplicity ↑p ↑(x - y) + multiplicity p n
    rw [Int.ofNat_sub (Nat.pow_le_pow_of_le_left hyx n)]
    -- ⊢ multiplicity (↑p) (↑(x ^ n) - ↑(y ^ n)) = multiplicity ↑p ↑(x - y) + multipl …
    rw [← Int.coe_nat_dvd] at hxy hx
    -- ⊢ multiplicity (↑p) (↑(x ^ n) - ↑(y ^ n)) = multiplicity ↑p ↑(x - y) + multipl …
    rw [Int.coe_nat_sub hyx] at *
    -- ⊢ multiplicity (↑p) (↑(x ^ n) - ↑(y ^ n)) = multiplicity (↑p) (↑x - ↑y) + mult …
    push_cast at *
    -- ⊢ multiplicity (↑p) (↑x ^ n - ↑y ^ n) = multiplicity (↑p) (↑x - ↑y) + multipli …
    exact Int.pow_sub_pow hp hp1 hxy hx n
    -- 🎉 no goals
  · simp only [Nat.sub_eq_zero_iff_le.mpr hyx,
      Nat.sub_eq_zero_iff_le.mpr (Nat.pow_le_pow_of_le_left hyx n), multiplicity.zero,
      PartENat.top_add]
#align multiplicity.nat.pow_sub_pow multiplicity.Nat.pow_sub_pow

theorem Nat.pow_add_pow {x y : ℕ} (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : ℕ} (hn : Odd n) :
    multiplicity p (x ^ n + y ^ n) = multiplicity p (x + y) + multiplicity p n := by
  iterate 2 rw [← Int.coe_nat_multiplicity]
  -- ⊢ multiplicity ↑p ↑(x ^ n + y ^ n) = multiplicity ↑p ↑(x + y) + multiplicity p n
  rw [← Int.coe_nat_dvd] at hxy hx
  -- ⊢ multiplicity ↑p ↑(x ^ n + y ^ n) = multiplicity ↑p ↑(x + y) + multiplicity p n
  push_cast at *
  -- ⊢ multiplicity (↑p) (↑x ^ n + ↑y ^ n) = multiplicity (↑p) (↑x + ↑y) + multipli …
  exact Int.pow_add_pow hp hp1 hxy hx hn
  -- 🎉 no goals
#align multiplicity.nat.pow_add_pow multiplicity.Nat.pow_add_pow

end LiftingTheExponent

end multiplicity

end CommRing

theorem pow_two_pow_sub_pow_two_pow [CommRing R] {x y : R} (n : ℕ) :
    x ^ 2 ^ n - y ^ 2 ^ n = (∏ i in Finset.range n, (x ^ 2 ^ i + y ^ 2 ^ i)) * (x - y) := by
  induction' n with d hd
  -- ⊢ x ^ 2 ^ Nat.zero - y ^ 2 ^ Nat.zero = (∏ i in range Nat.zero, (x ^ 2 ^ i + y …
  · simp only [pow_zero, pow_one, range_zero, prod_empty, one_mul, Nat.zero_eq]
    -- 🎉 no goals
  · suffices x ^ 2 ^ d.succ - y ^ 2 ^ d.succ = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d) by
      rw [this, hd, Finset.prod_range_succ, ← mul_assoc, mul_comm (x ^ 2 ^ d + y ^ 2 ^ d)]
    · rw [Nat.succ_eq_add_one]
      -- ⊢ x ^ 2 ^ (d + 1) - y ^ 2 ^ (d + 1) = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y …
      ring
      -- 🎉 no goals
#align pow_two_pow_sub_pow_two_pow pow_two_pow_sub_pow_two_pow

-- porting note: simplified proof because `fin_cases` was not available in that case
theorem Int.sq_mod_four_eq_one_of_odd {x : ℤ} : Odd x → x ^ 2 % 4 = 1 := by
  intro hx
  -- ⊢ x ^ 2 % 4 = 1
  unfold Odd at hx
  -- ⊢ x ^ 2 % 4 = 1
  rcases hx with ⟨_, rfl⟩
  -- ⊢ (2 * w✝ + 1) ^ 2 % 4 = 1
  ring_nf
  -- ⊢ (1 + w✝ * 4 + w✝ ^ 2 * 4) % 4 = 1
  rw [add_assoc, ← add_mul, Int.add_mul_emod_self]
  -- ⊢ 1 % 4 = 1
  norm_num
  -- 🎉 no goals
#align int.sq_mod_four_eq_one_of_odd Int.sq_mod_four_eq_one_of_odd

theorem Int.two_pow_two_pow_add_two_pow_two_pow {x y : ℤ} (hx : ¬2 ∣ x) (hxy : 4 ∣ x - y) (i : ℕ) :
    multiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑(1 : ℕ) := by
  have hx_odd : Odd x := by rwa [Int.odd_iff_not_even, even_iff_two_dvd]
  -- ⊢ multiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑1
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hxy)
  -- ⊢ multiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑1
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  -- ⊢ multiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑1
  refine' multiplicity.eq_coe_iff.mpr ⟨_, _⟩
  -- ⊢ 2 ^ 1 ∣ x ^ 2 ^ i + y ^ 2 ^ i
  · rw [pow_one, ← even_iff_two_dvd]
    -- ⊢ Even (x ^ 2 ^ i + y ^ 2 ^ i)
    exact hx_odd.pow.add_odd hy_odd.pow
    -- 🎉 no goals
  cases' i with i
  -- ⊢ ¬2 ^ (1 + 1) ∣ x ^ 2 ^ Nat.zero + y ^ 2 ^ Nat.zero
  · intro hxy'
    -- ⊢ False
    have : 2 * 2 ∣ 2 * x := by
      have := dvd_add hxy hxy'
      norm_num at *
      rw [two_mul]
      exact this
    have : 2 ∣ x := (mul_dvd_mul_iff_left (by norm_num)).mp this
    -- ⊢ False
    contradiction
    -- 🎉 no goals
  suffices ∀ x : ℤ, Odd x → x ^ 2 ^ (i + 1) % 4 = 1 by
    rw [show (2 ^ (1 + 1) : ℤ) = 4 by norm_num, Int.dvd_iff_emod_eq_zero, Int.add_emod,
      this _ hx_odd, this _ hy_odd]
    norm_num
  intro x hx
  -- ⊢ x ^ 2 ^ (i + 1) % 4 = 1
  rw [pow_succ, mul_comm, pow_mul, Int.sq_mod_four_eq_one_of_odd hx.pow]
  -- 🎉 no goals
#align int.two_pow_two_pow_add_two_pow_two_pow Int.two_pow_two_pow_add_two_pow_two_pow

theorem Int.two_pow_two_pow_sub_pow_two_pow {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x) :
    multiplicity 2 (x ^ 2 ^ n - y ^ 2 ^ n) = multiplicity 2 (x - y) + n := by
  simp only [pow_two_pow_sub_pow_two_pow n, multiplicity.mul Int.prime_two,
    multiplicity.Finset.prod Int.prime_two, add_comm, Nat.cast_one, Finset.sum_const,
    Finset.card_range, nsmul_one, Int.two_pow_two_pow_add_two_pow_two_pow hx hxy]
#align int.two_pow_two_pow_sub_pow_two_pow Int.two_pow_two_pow_sub_pow_two_pow

theorem Int.two_pow_sub_pow' {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x) :
    multiplicity 2 (x ^ n - y ^ n) = multiplicity 2 (x - y) + multiplicity (2 : ℤ) n := by
  have hx_odd : Odd x := by rwa [Int.odd_iff_not_even, even_iff_two_dvd]
  -- ⊢ multiplicity 2 (x ^ n - y ^ n) = multiplicity 2 (x - y) + multiplicity 2 ↑n
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by norm_num) hxy)
  -- ⊢ multiplicity 2 (x ^ n - y ^ n) = multiplicity 2 (x - y) + multiplicity 2 ↑n
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  -- ⊢ multiplicity 2 (x ^ n - y ^ n) = multiplicity 2 (x - y) + multiplicity 2 ↑n
  cases' n with n
  -- ⊢ multiplicity 2 (x ^ Nat.zero - y ^ Nat.zero) = multiplicity 2 (x - y) + mult …
  · simp only [pow_zero, sub_self, multiplicity.zero, Int.ofNat_zero, Nat.zero_eq, add_top]
    -- 🎉 no goals
  have h : (multiplicity 2 n.succ).Dom := multiplicity.finite_nat_iff.mpr ⟨by norm_num, n.succ_pos⟩
  -- ⊢ multiplicity 2 (x ^ Nat.succ n - y ^ Nat.succ n) = multiplicity 2 (x - y) +  …
  rcases multiplicity.eq_coe_iff.mp (PartENat.natCast_get h).symm with ⟨⟨k, hk⟩, hpn⟩
  -- ⊢ multiplicity 2 (x ^ Nat.succ n - y ^ Nat.succ n) = multiplicity 2 (x - y) +  …
  rw [hk, pow_mul, pow_mul, multiplicity.pow_sub_pow_of_prime,
    Int.two_pow_two_pow_sub_pow_two_pow _ hxy hx, ← hk, PartENat.natCast_get]
  · norm_cast
    -- 🎉 no goals
  · exact Int.prime_two
    -- 🎉 no goals
  · simpa only [even_iff_two_dvd] using hx_odd.pow.sub_odd hy_odd.pow
    -- 🎉 no goals
  · simpa only [even_iff_two_dvd, Int.odd_iff_not_even] using hx_odd.pow
    -- 🎉 no goals
  erw [Int.coe_nat_dvd]
  -- ⊢ ¬2 ∣ k
  -- `erw` to deal with `2 : ℤ` vs `(2 : ℕ) : ℤ`
  contrapose! hpn
  -- ⊢ 2 ^ (Part.get (multiplicity 2 (Nat.succ n)) h + 1) ∣ Nat.succ n
  rw [pow_succ']
  -- ⊢ 2 ^ Part.get (multiplicity 2 (Nat.succ n)) h * 2 ∣ Nat.succ n
  conv_rhs => rw [hk]
  -- ⊢ 2 ^ Part.get (multiplicity 2 (Nat.succ n)) h * 2 ∣ 2 ^ Part.get (multiplicit …
  exact mul_dvd_mul_left _ hpn
  -- 🎉 no goals
#align int.two_pow_sub_pow' Int.two_pow_sub_pow'

/-- **Lifting the exponent lemma** for `p = 2` -/
theorem Int.two_pow_sub_pow {x y : ℤ} {n : ℕ} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) (hn : Even n) :
    multiplicity 2 (x ^ n - y ^ n) + 1 =
      multiplicity 2 (x + y) + multiplicity 2 (x - y) + multiplicity (2 : ℤ) n := by
  have hy : Odd y := by
    rw [← even_iff_two_dvd, ← Int.odd_iff_not_even] at hx
    replace hxy := (@even_neg _ _ (x - y)).mpr (even_iff_two_dvd.mpr hxy)
    convert Even.add_odd hxy hx
    abel
  cases' hn with d hd
  -- ⊢ multiplicity 2 (x ^ n - y ^ n) + 1 = multiplicity 2 (x + y) + multiplicity 2 …
  subst hd
  -- ⊢ multiplicity 2 (x ^ (d + d) - y ^ (d + d)) + 1 = multiplicity 2 (x + y) + mu …
  simp only [← two_mul, pow_mul]
  -- ⊢ multiplicity 2 ((x ^ 2) ^ d - (y ^ 2) ^ d) + 1 = multiplicity 2 (x + y) + mu …
  have hxy4 : 4 ∣ x ^ 2 - y ^ 2 := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, Int.sq_mod_four_eq_one_of_odd _,
      Int.sq_mod_four_eq_one_of_odd hy]
    · norm_num
    · simp only [Int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff]
  rw [Int.two_pow_sub_pow' d hxy4 _, sq_sub_sq, ← Int.ofNat_mul_out, multiplicity.mul Int.prime_two,
    multiplicity.mul Int.prime_two]
  suffices multiplicity (2 : ℤ) ↑(2 : ℕ) = 1 by rw [this, add_comm (1 : PartENat), ← add_assoc]
  -- ⊢ multiplicity 2 ↑2 = 1
  · norm_cast
    -- ⊢ multiplicity 2 2 = 1
    rw [multiplicity.multiplicity_self _ _]
    -- ⊢ ¬IsUnit 2
    · apply Prime.not_unit
      -- ⊢ Prime 2
      simp only [← Nat.prime_iff, Nat.prime_two]
      -- 🎉 no goals
    · exact two_ne_zero
      -- 🎉 no goals
  · rw [← even_iff_two_dvd, ← Int.odd_iff_not_even]
    -- ⊢ Odd (x ^ 2)
    apply Odd.pow
    -- ⊢ Odd x
    simp only [Int.odd_iff_not_even, even_iff_two_dvd, hx, not_false_iff]
    -- 🎉 no goals
#align int.two_pow_sub_pow Int.two_pow_sub_pow

theorem Nat.two_pow_sub_pow {x y : ℕ} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : ℕ} (hn : Even n) :
    multiplicity 2 (x ^ n - y ^ n) + 1 =
      multiplicity 2 (x + y) + multiplicity 2 (x - y) + multiplicity 2 n := by
  obtain hyx | hyx := le_total y x
  -- ⊢ multiplicity 2 (x ^ n - y ^ n) + 1 = multiplicity 2 (x + y) + multiplicity 2 …
  · iterate 3 rw [← multiplicity.Int.coe_nat_multiplicity]
    -- ⊢ multiplicity ↑2 ↑(x ^ n - y ^ n) + 1 = multiplicity ↑2 ↑(x + y) + multiplici …
    simp only [Int.ofNat_sub hyx, Int.ofNat_sub (pow_le_pow_of_le_left' hyx _), Int.ofNat_add,
      Int.coe_nat_pow]
    rw [← Int.coe_nat_dvd] at hx
    -- ⊢ multiplicity (↑2) (↑x ^ n - ↑y ^ n) + 1 = multiplicity (↑2) (↑x + ↑y) + mult …
    rw [← Int.coe_nat_dvd, Int.ofNat_sub hyx] at hxy
    -- ⊢ multiplicity (↑2) (↑x ^ n - ↑y ^ n) + 1 = multiplicity (↑2) (↑x + ↑y) + mult …
    convert Int.two_pow_sub_pow hxy hx hn using 2
    -- ⊢ multiplicity 2 n = multiplicity 2 ↑n
    rw [← multiplicity.Int.coe_nat_multiplicity]
    -- ⊢ multiplicity ↑2 ↑n = multiplicity 2 ↑n
    rfl
    -- 🎉 no goals
  · simp only [Nat.sub_eq_zero_iff_le.mpr hyx,
      Nat.sub_eq_zero_iff_le.mpr (pow_le_pow_of_le_left' hyx n), multiplicity.zero,
      PartENat.top_add, PartENat.add_top]
#align nat.two_pow_sub_pow Nat.two_pow_sub_pow

namespace padicValNat

variable {x y : ℕ}

theorem pow_two_sub_pow (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : ℕ} (hn : 0 < n)
    (hneven : Even n) :
    padicValNat 2 (x ^ n - y ^ n) + 1 =
      padicValNat 2 (x + y) + padicValNat 2 (x - y) + padicValNat 2 n := by
  simp only [← PartENat.natCast_inj, Nat.cast_add]
  -- ⊢ ↑(padicValNat 2 (x ^ n - y ^ n)) + ↑1 = ↑(padicValNat 2 (x + y)) + ↑(padicVa …
  iterate 4 rw [padicValNat_def, PartENat.natCast_get]
  · convert Nat.two_pow_sub_pow hxy hx hneven using 2
    -- 🎉 no goals
  · exact hn
    -- 🎉 no goals
  · exact Nat.sub_pos_of_lt hyx
    -- 🎉 no goals
  · linarith
    -- 🎉 no goals
  · simp only [tsub_pos_iff_lt, pow_lt_pow_of_lt_left hyx (@zero_le' _ y _) hn]
    -- 🎉 no goals
#align padic_val_nat.pow_two_sub_pow padicValNat.pow_two_sub_pow

variable {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p)

theorem pow_sub_pow (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : 0 < n) :
    padicValNat p (x ^ n - y ^ n) = padicValNat p (x - y) + padicValNat p n := by
  rw [← PartENat.natCast_inj, Nat.cast_add]
  -- ⊢ ↑(padicValNat p (x ^ n - y ^ n)) = ↑(padicValNat p (x - y)) + ↑(padicValNat  …
  iterate 3 rw [padicValNat_def, PartENat.natCast_get]
  · exact multiplicity.Nat.pow_sub_pow hp.out hp1 hxy hx n
    -- 🎉 no goals
  · exact hn
    -- 🎉 no goals
  · exact Nat.sub_pos_of_lt hyx
    -- 🎉 no goals
  · exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_of_lt_left hyx hn)
    -- 🎉 no goals
#align padic_val_nat.pow_sub_pow padicValNat.pow_sub_pow

theorem pow_add_pow (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : ℕ} (hn : Odd n) :
    padicValNat p (x ^ n + y ^ n) = padicValNat p (x + y) + padicValNat p n := by
  cases' y with y
  -- ⊢ padicValNat p (x ^ n + Nat.zero ^ n) = padicValNat p (x + Nat.zero) + padicV …
  · contradiction
    -- 🎉 no goals
  rw [← PartENat.natCast_inj, Nat.cast_add]
  -- ⊢ ↑(padicValNat p (x ^ n + Nat.succ y ^ n)) = ↑(padicValNat p (x + Nat.succ y) …
  iterate 3 rw [padicValNat_def, PartENat.natCast_get]
  · exact multiplicity.Nat.pow_add_pow hp.out hp1 hxy hx hn
    -- 🎉 no goals
  · exact Odd.pos hn
    -- 🎉 no goals
  · simp only [add_pos_iff, Nat.succ_pos', or_true_iff]
    -- 🎉 no goals
  · exact Nat.lt_add_left _ _ _ (pow_pos y.succ_pos _)
    -- 🎉 no goals
#align padic_val_nat.pow_add_pow padicValNat.pow_add_pow

end padicValNat
