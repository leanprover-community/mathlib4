/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.Multiplicity

#align_import data.nat.multiplicity from "leanprover-community/mathlib"@"ceb887ddf3344dab425292e497fa2af91498437c"

/-!
# Natural number multiplicity

This file contains lemmas about the multiplicity function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.

## Multiplicity calculations

* `Nat.Prime.multiplicity_factorial`: Legendre's Theorem. The multiplicity of `p` in `n!` is
  `n/p + ... + n/p^b` for any `b` such that `n/p^(b + 1) = 0`. See `padicValNat_factorial` for this
  result stated in the language of `p`-adic valuations and
  `sub_one_mul_padicValNat_factorial_eq_sub_sum_digits` for a related result.
* `Nat.Prime.multiplicity_factorial_mul`: The multiplicity of `p` in `(p * n)!` is `n` more than
  that of `n!`.
* `Nat.Prime.multiplicity_choose`: Kummer's Theorem. The multiplicity of `p` in `n.choose k` is the
   number of carries  when `k` and `n - k` are added in base `p`. See `padicValNat_choose` for the
   same result but stated in the language of `p`-adic valuations.

## Other declarations

* `Nat.multiplicity_eq_card_pow_dvd`: The multiplicity of `m` in `n` is the number of positive
  natural numbers `i` such that `m ^ i` divides `n`.
* `Nat.multiplicity_two_factorial_lt`: The multiplicity of `2` in `n!` is strictly less than `n`.
* `Nat.Prime.multiplicity_something`: Specialization of `multiplicity.something` to a prime in the
  naturals. Avoids having to provide `p ≠ 1` and other trivialities, along with translating between
  `Prime` and `Nat.Prime`.

## Tags

Legendre, p-adic
-/


open Finset Nat multiplicity

open BigOperators Nat

namespace Nat

/-- The multiplicity of `m` in `n` is the number of positive natural numbers `i` such that `m ^ i`
divides `n`. This set is expressed by filtering `Ico 1 b` where `b` is any bound greater than
`log m n`. -/
theorem multiplicity_eq_card_pow_dvd {m n b : ℕ} (hm : m ≠ 1) (hn : 0 < n) (hb : log m n < b) :
    multiplicity m n = ↑((Finset.Ico 1 b).filter fun i => m ^ i ∣ n).card :=
  calc
    multiplicity m n = ↑(Ico 1 <| (multiplicity m n).get (finite_nat_iff.2 ⟨hm, hn⟩) + 1).card := by
      simp
      -- 🎉 no goals
    _ = ↑((Finset.Ico 1 b).filter fun i => m ^ i ∣ n).card :=
      congr_arg _ <|
        congr_arg card <|
          Finset.ext fun i => by
            rw [mem_filter, mem_Ico, mem_Ico, lt_succ_iff, ← @PartENat.coe_le_coe i,
              PartENat.natCast_get, ← pow_dvd_iff_le_multiplicity, and_right_comm]
            refine' (and_iff_left_of_imp fun h => lt_of_le_of_lt _ hb).symm
            -- ⊢ i ≤ log m n
            cases' m with m
            -- ⊢ i ≤ log zero n
            · rw [zero_eq, zero_pow, zero_dvd_iff] at h
              -- ⊢ i ≤ log zero n
              exacts [(hn.ne' h.2).elim, h.1]
              -- 🎉 no goals
            exact le_log_of_pow_le (one_lt_iff_ne_zero_and_ne_one.2 ⟨m.succ_ne_zero, hm⟩)
                (le_of_dvd hn h.2)
#align nat.multiplicity_eq_card_pow_dvd Nat.multiplicity_eq_card_pow_dvd

namespace Prime

theorem multiplicity_one {p : ℕ} (hp : p.Prime) : multiplicity p 1 = 0 :=
  multiplicity.one_right hp.prime.not_unit
#align nat.prime.multiplicity_one Nat.Prime.multiplicity_one

theorem multiplicity_mul {p m n : ℕ} (hp : p.Prime) :
    multiplicity p (m * n) = multiplicity p m + multiplicity p n :=
  multiplicity.mul hp.prime
#align nat.prime.multiplicity_mul Nat.Prime.multiplicity_mul

theorem multiplicity_pow {p m n : ℕ} (hp : p.Prime) :
    multiplicity p (m ^ n) = n • multiplicity p m :=
  multiplicity.pow hp.prime
#align nat.prime.multiplicity_pow Nat.Prime.multiplicity_pow

theorem multiplicity_self {p : ℕ} (hp : p.Prime) : multiplicity p p = 1 :=
  multiplicity.multiplicity_self hp.prime.not_unit hp.ne_zero
#align nat.prime.multiplicity_self Nat.Prime.multiplicity_self

theorem multiplicity_pow_self {p n : ℕ} (hp : p.Prime) : multiplicity p (p ^ n) = n :=
  multiplicity.multiplicity_pow_self hp.ne_zero hp.prime.not_unit n
#align nat.prime.multiplicity_pow_self Nat.Prime.multiplicity_pow_self

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
theorem multiplicity_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → multiplicity p n ! = (∑ i in Ico 1 b, n / p ^ i : ℕ)
  | 0, b, _ => by simp [Ico, hp.multiplicity_one]
                  -- 🎉 no goals
  | n + 1, b, hb =>
    calc
      multiplicity p (n + 1)! = multiplicity p n ! + multiplicity p (n + 1) := by
        rw [factorial_succ, hp.multiplicity_mul, add_comm]
        -- 🎉 no goals
      _ = (∑ i in Ico 1 b, n / p ^ i : ℕ) +
            ((Finset.Ico 1 b).filter fun i => p ^ i ∣ n + 1).card := by
        rw [multiplicity_factorial hp ((log_mono_right <| le_succ _).trans_lt hb), ←
          multiplicity_eq_card_pow_dvd hp.ne_one (succ_pos _) hb]
      _ = (∑ i in Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) : ℕ) := by
        rw [sum_add_distrib, sum_boole]
        -- ⊢ ↑(∑ i in Ico 1 b, n / p ^ i) + ↑(card (filter (fun i => p ^ i ∣ n + 1) (Ico  …
        simp
        -- 🎉 no goals
      _ = (∑ i in Ico 1 b, (n + 1) / p ^ i : ℕ) :=
        congr_arg _ <| Finset.sum_congr rfl fun _ _ => (succ_div _ _).symm
#align nat.prime.multiplicity_factorial Nat.Prime.multiplicity_factorial

/-- The multiplicity of `p` in `(p * (n + 1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
theorem multiplicity_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n + 1) + 1 := by
  have hp' := hp.prime
  -- ⊢ multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n  …
  have h0 : 2 ≤ p := hp.two_le
  -- ⊢ multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n  …
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_left _ _
  -- ⊢ multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n  …
  have h2 : p * n + 1 ≤ p * (n + 1)
  -- ⊢ p * n + 1 ≤ p * (n + 1)
  · linarith
    -- 🎉 no goals
  have h3 : p * n + 1 ≤ p * (n + 1) + 1
  -- ⊢ p * n + 1 ≤ p * (n + 1) + 1
  · linarith
    -- 🎉 no goals
  have hm : multiplicity p (p * n)! ≠ ⊤ := by
    rw [Ne.def, eq_top_iff_not_finite, Classical.not_not, finite_nat_iff]
    exact ⟨hp.ne_one, factorial_pos _⟩
  revert hm
  -- ⊢ multiplicity p (p * n)! ≠ ⊤ → multiplicity p (p * (n + 1))! = multiplicity p …
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), multiplicity p m = 0 := by
    intro m hm
    rw [multiplicity_eq_zero, ← not_dvd_iff_between_consec_multiples _ hp.pos]
    rw [mem_Ico] at hm
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩
  simp_rw [← prod_Ico_id_eq_factorial, multiplicity.Finset.prod hp', ← sum_Ico_consecutive _ h1 h3,
    add_assoc]
  intro h
  -- ⊢ ∑ x in Ico 1 (p * n + 1), multiplicity p x + ∑ x in Ico (p * n + 1) (p * (n  …
  rw [PartENat.add_left_cancel_iff h, sum_Ico_succ_top h2, multiplicity.mul hp',
    hp.multiplicity_self, sum_congr rfl h4, sum_const_zero, zero_add, add_comm (1 : PartENat)]
#align nat.prime.multiplicity_factorial_mul_succ Nat.Prime.multiplicity_factorial_mul_succ

/-- The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`. -/
theorem multiplicity_factorial_mul {n p : ℕ} (hp : p.Prime) :
    multiplicity p (p * n)! = multiplicity p n ! + n := by
  induction' n with n ih
  -- ⊢ multiplicity p (p * zero)! = multiplicity p zero ! + ↑zero
  · simp
    -- 🎉 no goals
  · simp only [succ_eq_add_one, multiplicity.mul, hp, hp.prime, ih, multiplicity_factorial_mul_succ,
      ← add_assoc, Nat.cast_one, Nat.cast_add, factorial_succ]
    congr 1
    -- ⊢ multiplicity p n ! + ↑n + multiplicity p (n + 1) = multiplicity p (n + 1) +  …
    rw [add_comm, add_assoc]
    -- 🎉 no goals
#align nat.prime.multiplicity_factorial_mul Nat.Prime.multiplicity_factorial_mul

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater than `log p n` -/
theorem pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.Prime) (hbn : log p n < b) :
    p ^ r ∣ n ! ↔ r ≤ ∑ i in Ico 1 b, n / p ^ i := by
  rw [← PartENat.coe_le_coe, ← hp.multiplicity_factorial hbn, ← pow_dvd_iff_le_multiplicity]
  -- 🎉 no goals
#align nat.prime.pow_dvd_factorial_iff Nat.Prime.pow_dvd_factorial_iff

theorem multiplicity_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) :
    multiplicity p n ! ≤ (n / (p - 1) : ℕ) := by
  rw [hp.multiplicity_factorial (lt_succ_self _), PartENat.coe_le_coe]
  -- ⊢ ∑ i in Ico 1 (succ (log p n)), n / p ^ i ≤ n / (p - 1)
  exact Nat.geom_sum_Ico_le hp.two_le _ _
  -- 🎉 no goals
#align nat.prime.multiplicity_factorial_le_div_pred Nat.Prime.multiplicity_factorial_le_div_pred

theorem multiplicity_choose_aux {p n b k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    ∑ i in Finset.Ico 1 b, n / p ^ i =
      ((∑ i in Finset.Ico 1 b, k / p ^ i) + ∑ i in Finset.Ico 1 b, (n - k) / p ^ i) +
        ((Finset.Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card :=
  calc
    ∑ i in Finset.Ico 1 b, n / p ^ i = ∑ i in Finset.Ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [add_tsub_cancel_of_le hkn]
      -- 🎉 no goals
    _ = ∑ i in Finset.Ico 1 b,
          (k / p ^ i + (n - k) / p ^ i + if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0) :=
      by simp only [Nat.add_div (pow_pos hp.pos _)]
         -- 🎉 no goals
    _ = _ := by simp [sum_add_distrib, sum_boole]
                -- 🎉 no goals
#align nat.prime.multiplicity_choose_aux Nat.Prime.multiplicity_choose_aux

/-- The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
theorem multiplicity_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
    multiplicity p (choose n k) =
      ((Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card := by
  have h₁ :
    multiplicity p (choose n k) + multiplicity p (k ! * (n - k)!) =
      ((Finset.Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card +
        multiplicity p (k ! * (n - k)!) := by
    rw [← hp.multiplicity_mul, ← mul_assoc, choose_mul_factorial_mul_factorial hkn,
      hp.multiplicity_factorial hnb, hp.multiplicity_mul,
      hp.multiplicity_factorial ((log_mono_right hkn).trans_lt hnb),
      hp.multiplicity_factorial (lt_of_le_of_lt (log_mono_right tsub_le_self) hnb),
      multiplicity_choose_aux hp hkn]
    simp [add_comm]
  refine (PartENat.add_right_cancel_iff ?_).1 h₁
  -- ⊢ multiplicity p (k ! * (n - k)!) ≠ ⊤
  apply PartENat.ne_top_iff_dom.2
  -- ⊢ (multiplicity p (k ! * (n - k)!)).Dom
  exact finite_nat_iff.2 ⟨hp.ne_one, mul_pos (factorial_pos k) (factorial_pos (n - k))⟩
  -- 🎉 no goals
#align nat.prime.multiplicity_choose Nat.Prime.multiplicity_choose

/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
theorem multiplicity_le_multiplicity_choose_add {p : ℕ} (hp : p.Prime) :
    ∀ n k : ℕ, multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k
  | _, 0 => by simp
               -- 🎉 no goals
  | 0, _ + 1 => by simp
                   -- 🎉 no goals
  | n + 1, k + 1 => by
    rw [← hp.multiplicity_mul]
    -- ⊢ multiplicity p (n + 1) ≤ multiplicity p (choose (n + 1) (k + 1) * (k + 1))
    refine' multiplicity_le_multiplicity_of_dvd_right _
    -- ⊢ n + 1 ∣ choose (n + 1) (k + 1) * (k + 1)
    rw [← succ_mul_choose_eq]
    -- ⊢ n + 1 ∣ succ n * choose n k
    exact dvd_mul_right _ _
    -- 🎉 no goals
#align nat.prime.multiplicity_le_multiplicity_choose_add Nat.Prime.multiplicity_le_multiplicity_choose_add

variable {p n k : ℕ}

theorem multiplicity_choose_prime_pow_add_multiplicity (hp : p.Prime) (hkn : k ≤ p ^ n)
    (hk0 : k ≠ 0) : multiplicity p (choose (p ^ n) k) + multiplicity p k = n :=
  le_antisymm
    (by
      have hdisj :
        Disjoint ((Ico 1 n.succ).filter fun i => p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i)
          ((Ico 1 n.succ).filter fun i => p ^ i ∣ k) := by
        simp (config := { contextual := true }) [disjoint_right, *, dvd_iff_mod_eq_zero,
          Nat.mod_lt _ (pow_pos hp.pos _)]
      rw [multiplicity_choose hp hkn (lt_succ_self _),
        multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) hk0.bot_lt
          (lt_succ_of_le (log_mono_right hkn)),
        ← Nat.cast_add, PartENat.coe_le_coe, log_pow hp.one_lt, ← card_disjoint_union hdisj,
        filter_union_right]
      have filter_le_Ico := (Ico 1 n.succ).card_filter_le
        fun x => p ^ x ≤ k % p ^ x + (p ^ n - k) % p ^ x ∨ p ^ x ∣ k
      rwa [card_Ico 1 n.succ] at filter_le_Ico)
      -- 🎉 no goals
    (by rw [← hp.multiplicity_pow_self]; exact multiplicity_le_multiplicity_choose_add hp _ _)
        -- ⊢ multiplicity p (p ^ n) ≤ multiplicity p (choose (p ^ n) k) + multiplicity p k
                                         -- 🎉 no goals
#align nat.prime.multiplicity_choose_prime_pow_add_multiplicity Nat.Prime.multiplicity_choose_prime_pow_add_multiplicity

theorem multiplicity_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    multiplicity p (choose (p ^ n) k) =
      ↑(n - (multiplicity p k).get (finite_nat_iff.2 ⟨hp.ne_one, hk0.bot_lt⟩)) :=
  PartENat.eq_natCast_sub_of_add_eq_natCast <|
    multiplicity_choose_prime_pow_add_multiplicity hp hkn hk0
#align nat.prime.multiplicity_choose_prime_pow Nat.Prime.multiplicity_choose_prime_pow

theorem dvd_choose_pow (hp : Prime p) (hk : k ≠ 0) (hkp : k ≠ p ^ n) : p ∣ (p ^ n).choose k := by
  obtain hkp | hkp := hkp.symm.lt_or_lt
  -- ⊢ p ∣ choose (p ^ n) k
  · simp [choose_eq_zero_of_lt hkp]
    -- 🎉 no goals
  refine' multiplicity_ne_zero.1 fun h => hkp.not_le <| Nat.le_of_dvd hk.bot_lt _
  -- ⊢ p ^ n ∣ k
  have H := hp.multiplicity_choose_prime_pow_add_multiplicity hkp.le hk
  -- ⊢ p ^ n ∣ k
  rw [h, zero_add, eq_coe_iff] at H
  -- ⊢ p ^ n ∣ k
  exact H.1
  -- 🎉 no goals
#align nat.prime.dvd_choose_pow Nat.Prime.dvd_choose_pow

theorem dvd_choose_pow_iff (hp : Prime p) : p ∣ (p ^ n).choose k ↔ k ≠ 0 ∧ k ≠ p ^ n := by
  refine' ⟨fun h => ⟨_, _⟩, fun h => dvd_choose_pow hp h.1 h.2⟩ <;> rintro rfl <;>
  -- ⊢ k ≠ 0
                                                                    -- ⊢ False
                                                                    -- ⊢ False
    simp [hp.ne_one] at h
    -- 🎉 no goals
    -- 🎉 no goals
#align nat.prime.dvd_choose_pow_iff Nat.Prime.dvd_choose_pow_iff

end Prime

theorem multiplicity_two_factorial_lt : ∀ {n : ℕ} (_ : n ≠ 0), multiplicity 2 n ! < n := by
  have h2 := prime_two.prime
  -- ⊢ ∀ {n : ℕ}, n ≠ 0 → multiplicity 2 n ! < ↑n
  refine' binaryRec _ _
  -- ⊢ 0 ≠ 0 → multiplicity 2 0! < ↑0
  · exact fun h => False.elim <| h rfl
    -- 🎉 no goals
  · intro b n ih h
    -- ⊢ multiplicity 2 (bit b n)! < ↑(bit b n)
    by_cases hn : n = 0
    -- ⊢ multiplicity 2 (bit b n)! < ↑(bit b n)
    · subst hn
      -- ⊢ multiplicity 2 (bit b 0)! < ↑(bit b 0)
      simp only [ne_eq, bit_eq_zero, true_and, Bool.not_eq_false] at h
      -- ⊢ multiplicity 2 (bit b 0)! < ↑(bit b 0)
      simp only [h, bit_true, bit1_zero, factorial, mul_one, Nat.isUnit_iff, cast_one]
      -- ⊢ multiplicity 2 (succ 0) < 1
      rw [Prime.multiplicity_one]
      -- ⊢ 0 < 1
      simp only [zero_lt_one]
      -- ⊢ Prime 2
      decide
      -- 🎉 no goals
    have : multiplicity 2 (2 * n)! < (2 * n : ℕ) := by
      rw [prime_two.multiplicity_factorial_mul]
      refine' (PartENat.add_lt_add_right (ih hn) (PartENat.natCast_ne_top _)).trans_le _
      rw [two_mul]
      norm_cast
    cases b
    -- ⊢ multiplicity 2 (bit false n)! < ↑(bit false n)
    · simpa [bit0_eq_two_mul n]
      -- 🎉 no goals
    · suffices multiplicity 2 (2 * n + 1) + multiplicity 2 (2 * n)! < ↑(2 * n) + 1 by
        simpa [succ_eq_add_one, multiplicity.mul, h2, prime_two, Nat.bit1_eq_succ_bit0,
          bit0_eq_two_mul n]
      rw [multiplicity_eq_zero.2 (two_not_dvd_two_mul_add_one n), zero_add]
      -- ⊢ multiplicity 2 (2 * n)! < ↑(2 * n) + 1
      refine' this.trans _
      -- ⊢ ↑(2 * n) < ↑(2 * n) + 1
      exact_mod_cast lt_succ_self _
      -- 🎉 no goals
#align nat.multiplicity_two_factorial_lt Nat.multiplicity_two_factorial_lt

end Nat
