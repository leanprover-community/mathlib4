/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.OrderOfElement

#align_import algebra.char_p.basic from "leanprover-community/mathlib"@"47a1a73351de8dd6c8d3d32b569c8e434b03ca47"

/-!
# Characteristic of semirings
-/


universe u v

open Finset

variable {R : Type*}

namespace Commute

variable [Semiring R] {p : ℕ} {x y : R}

protected theorem add_pow_prime_pow_eq (hp : p.Prime) (h : Commute x y) (n : ℕ) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k ∈ Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) := by
  trans x ^ p ^ n + y ^ p ^ n + ∑ k ∈ Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k
  · simp_rw [h.add_pow, ← Nat.Ico_zero_eq_range, Nat.Ico_succ_right, Icc_eq_cons_Ico (zero_le _),
      Finset.sum_cons, Ico_eq_cons_Ioo (pow_pos hp.pos _), Finset.sum_cons, tsub_self, tsub_zero,
      pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, mul_one, one_mul, ← add_assoc]
  · congr 1
    simp_rw [Finset.mul_sum, Nat.cast_comm, mul_assoc _ _ (p : R), ← Nat.cast_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_Ioo] at hi
    rw [Nat.div_mul_cancel (hp.dvd_choose_pow hi.1.ne' hi.2.ne)]
#align commute.add_pow_prime_pow_eq Commute.add_pow_prime_pow_eq

protected theorem add_pow_prime_eq (hp : p.Prime) (h : Commute x y) :
    (x + y) ^ p =
      x ^ p + y ^ p + p * ∑ k ∈ Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) := by
  simpa using h.add_pow_prime_pow_eq hp 1
#align commute.add_pow_prime_eq Commute.add_pow_prime_eq

protected theorem exists_add_pow_prime_pow_eq (hp : p.Prime) (h : Commute x y) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
  ⟨_, h.add_pow_prime_pow_eq hp n⟩
#align commute.exists_add_pow_prime_pow_eq Commute.exists_add_pow_prime_pow_eq

protected theorem exists_add_pow_prime_eq (hp : p.Prime) (h : Commute x y) :
    ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * r :=
  ⟨_, h.add_pow_prime_eq hp⟩
#align commute.exists_add_pow_prime_eq Commute.exists_add_pow_prime_eq

end Commute

section CommSemiring

variable [CommSemiring R] {p : ℕ} {x y : R}

theorem add_pow_prime_pow_eq (hp : p.Prime) (x y : R) (n : ℕ) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k ∈ Finset.Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) :=
  (Commute.all x y).add_pow_prime_pow_eq hp n
#align add_pow_prime_pow_eq add_pow_prime_pow_eq

theorem add_pow_prime_eq (hp : p.Prime) (x y : R) :
    (x + y) ^ p =
      x ^ p + y ^ p + p * ∑ k ∈ Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) :=
  (Commute.all x y).add_pow_prime_eq hp
#align add_pow_prime_eq add_pow_prime_eq

theorem exists_add_pow_prime_pow_eq (hp : p.Prime) (x y : R) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
  (Commute.all x y).exists_add_pow_prime_pow_eq hp n
#align exists_add_pow_prime_pow_eq exists_add_pow_prime_pow_eq

theorem exists_add_pow_prime_eq (hp : p.Prime) (x y : R) :
    ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * r :=
  (Commute.all x y).exists_add_pow_prime_eq hp
#align exists_add_pow_prime_eq exists_add_pow_prime_eq

end CommSemiring

variable (R)

@[simp]
theorem CharP.cast_card_eq_zero [AddGroupWithOne R] [Fintype R] : (Fintype.card R : R) = 0 := by
  rw [← nsmul_one, card_nsmul_eq_zero]
#align char_p.cast_card_eq_zero CharP.cast_card_eq_zero

theorem CharP.addOrderOf_one (R) [Semiring R] : CharP R (addOrderOf (1 : R)) :=
  ⟨fun n => by rw [← Nat.smul_one_eq_cast, addOrderOf_dvd_iff_nsmul_eq_zero]⟩
#align char_p.add_order_of_one CharP.addOrderOf_one

theorem add_pow_char_of_commute [Semiring R] {p : ℕ} [hp : Fact p.Prime] [CharP R p] (x y : R)
    (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p := by
  let ⟨r, hr⟩ := h.exists_add_pow_prime_eq hp.out
  simp [hr]
#align add_pow_char_of_commute add_pow_char_of_commute

theorem add_pow_char_pow_of_commute [Semiring R] {p n : ℕ} [hp : Fact p.Prime] [CharP R p]
    (x y : R) (h : Commute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by
  let ⟨r, hr⟩ := h.exists_add_pow_prime_pow_eq hp.out n
  simp [hr]
#align add_pow_char_pow_of_commute add_pow_char_pow_of_commute

theorem sub_pow_char_of_commute [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R)
    (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p := by
  rw [eq_sub_iff_add_eq, ← add_pow_char_of_commute _ _ _ (Commute.sub_left h rfl)]
  simp
#align sub_pow_char_of_commute sub_pow_char_of_commute

theorem sub_pow_char_pow_of_commute [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R)
    (h : Commute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      rw [pow_succ, pow_mul, pow_mul, pow_mul, n_ih]
      apply sub_pow_char_of_commute; apply Commute.pow_pow h
#align sub_pow_char_pow_of_commute sub_pow_char_pow_of_commute

theorem add_pow_char [CommSemiring R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) :
    (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_char_of_commute _ _ _ (Commute.all _ _)
#align add_pow_char add_pow_char

theorem add_pow_char_pow [CommSemiring R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  add_pow_char_pow_of_commute _ _ _ (Commute.all _ _)
#align add_pow_char_pow add_pow_char_pow

theorem sub_pow_char [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) :
    (x - y) ^ p = x ^ p - y ^ p :=
  sub_pow_char_of_commute _ _ _ (Commute.all _ _)
#align sub_pow_char sub_pow_char

theorem sub_pow_char_pow [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sub_pow_char_pow_of_commute _ _ _ (Commute.all _ _)
#align sub_pow_char_pow sub_pow_char_pow

theorem CharP.neg_one_pow_char [Ring R] (p : ℕ) [CharP R p] [Fact p.Prime] :
    (-1 : R) ^ p = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow p]
  rw [← add_pow_char_of_commute R _ _ (Commute.one_right _), add_left_neg,
    zero_pow (Fact.out (p := Nat.Prime p)).ne_zero]
#align char_p.neg_one_pow_char CharP.neg_one_pow_char

theorem CharP.neg_one_pow_char_pow [Ring R] (p n : ℕ) [CharP R p] [Fact p.Prime] :
    (-1 : R) ^ p ^ n = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow (p ^ n)]
  rw [← add_pow_char_pow_of_commute R _ _ (Commute.one_right _), add_left_neg,
    zero_pow (pow_ne_zero _ (Fact.out (p := Nat.Prime p)).ne_zero)]
#align char_p.neg_one_pow_char_pow CharP.neg_one_pow_char_pow

namespace CharP

section

variable [NonAssocRing R]

/-- The characteristic of a finite ring cannot be zero. -/
theorem char_ne_zero_of_finite (p : ℕ) [CharP R p] [Finite R] : p ≠ 0 := by
  rintro rfl
  haveI : CharZero R := charP_to_charZero R
  cases nonempty_fintype R
  exact absurd Nat.cast_injective (not_injective_infinite_finite ((↑) : ℕ → R))
#align char_p.char_ne_zero_of_finite CharP.char_ne_zero_of_finite

theorem ringChar_ne_zero_of_finite [Finite R] : ringChar R ≠ 0 :=
  char_ne_zero_of_finite R (ringChar R)
#align char_p.ring_char_ne_zero_of_finite CharP.ringChar_ne_zero_of_finite

end

section Ring

variable [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]

theorem char_is_prime (p : ℕ) [CharP R p] : p.Prime :=
  Or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_finite R p)
#align char_p.char_is_prime CharP.char_is_prime

end Ring
end CharP

section

variable [NonAssocRing R] [Fintype R] (n : ℕ)

theorem charP_of_ne_zero (hn : Fintype.card R = n) (hR : ∀ i < n, (i : R) = 0 → i = 0) :
    CharP R n :=
  { cast_eq_zero_iff' := by
      have H : (n : R) = 0 := by rw [← hn, CharP.cast_card_eq_zero]
      intro k
      constructor
      · intro h
        rw [← Nat.mod_add_div k n, Nat.cast_add, Nat.cast_mul, H, zero_mul,
          add_zero] at h
        rw [Nat.dvd_iff_mod_eq_zero]
        apply hR _ (Nat.mod_lt _ _) h
        rw [← hn, gt_iff_lt, Fintype.card_pos_iff]
        exact ⟨0⟩
      · rintro ⟨k, rfl⟩
        rw [Nat.cast_mul, H, zero_mul] }
#align char_p_of_ne_zero charP_of_ne_zero

theorem charP_of_prime_pow_injective (R) [Ring R] [Fintype R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
    (hn : Fintype.card R = p ^ n) (hR : ∀ i ≤ n, (p : R) ^ i = 0 → i = n) : CharP R (p ^ n) := by
  obtain ⟨c, hc⟩ := CharP.exists R
  have hcpn : c ∣ p ^ n := by rw [← CharP.cast_eq_zero_iff R c, ← hn, CharP.cast_card_eq_zero]
  obtain ⟨i, hi, hc⟩ : ∃ i ≤ n, c = p ^ i := by rwa [Nat.dvd_prime_pow hp.1] at hcpn
  obtain rfl : i = n := by
    apply hR i hi
    rw [← Nat.cast_pow, ← hc, CharP.cast_eq_zero]
  rwa [← hc]
#align char_p_of_prime_pow_injective charP_of_prime_pow_injective

end
