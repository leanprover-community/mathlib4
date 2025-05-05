/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Digits
import Mathlib.RingTheory.Multiplicity


/-!
# Natural number multiplicity

This file contains lemmas about the multiplicity function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.

## Multiplicity calculations

* `Nat.Prime.multiplicity_factorial`: Legendre's Theorem. The multiplicity of `p` in `n!` is
  `n / p + ... + n / p ^ b` for any `b` such that `n / p ^ (b + 1) = 0`. See `padicValNat_factorial`
  for this result stated in the language of `p`-adic valuations and
  `sub_one_mul_padicValNat_factorial` for a related result.
* `Nat.Prime.multiplicity_factorial_mul`: The multiplicity of `p` in `(p * n)!` is `n` more than
  that of `n!`.
* `Nat.Prime.multiplicity_choose`: Kummer's Theorem. The multiplicity of `p` in `n.choose k` is the
   number of carries when `k` and `n - k` are added in base `p`. See `padicValNat_choose` for the
   same result but stated in the language of `p`-adic valuations and
   `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` for a related result.

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


open Finset Nat

open Nat

namespace Nat

/-- The multiplicity of `m` in `n` is the number of positive natural numbers `i` such that `m ^ i`
divides `n`. This set is expressed by filtering `Ico 1 b` where `b` is any bound greater than
`log m n`. -/
theorem emultiplicity_eq_card_pow_dvd {m n b : ℕ} (hm : m ≠ 1) (hn : 0 < n) (hb : log m n < b) :
    emultiplicity m n = #{i ∈ Ico 1 b | m ^ i ∣ n} :=
  have fin := Nat.finiteMultiplicity_iff.2 ⟨hm, hn⟩
  calc
    emultiplicity m n = #(Ico 1 <| multiplicity m n + 1) := by
      simp [fin.emultiplicity_eq_multiplicity]
    _ = #{i ∈ Ico 1 b | m ^ i ∣ n} :=
      congr_arg _ <|
        congr_arg card <|
          Finset.ext fun i => by
            simp only [mem_Ico, Nat.lt_succ_iff,
              fin.pow_dvd_iff_le_multiplicity, mem_filter,
              and_assoc, and_congr_right_iff, iff_and_self]
            intro hi h
            rw [← fin.pow_dvd_iff_le_multiplicity] at h
            rcases m with - | m
            · rw [zero_pow, zero_dvd_iff] at h
              exacts [(hn.ne' h).elim, one_le_iff_ne_zero.1 hi]
            refine LE.le.trans_lt ?_ hb
            exact le_log_of_pow_le (one_lt_iff_ne_zero_and_ne_one.2 ⟨m.succ_ne_zero, hm⟩)
                (le_of_dvd hn h)

namespace Prime

theorem emultiplicity_one {p : ℕ} (hp : p.Prime) : emultiplicity p 1 = 0 :=
  emultiplicity_of_one_right hp.prime.not_unit

theorem emultiplicity_mul {p m n : ℕ} (hp : p.Prime) :
    emultiplicity p (m * n) = emultiplicity p m + emultiplicity p n :=
  _root_.emultiplicity_mul hp.prime

theorem emultiplicity_pow {p m n : ℕ} (hp : p.Prime) :
    emultiplicity p (m ^ n) = n * emultiplicity p m :=
  _root_.emultiplicity_pow hp.prime

theorem emultiplicity_self {p : ℕ} (hp : p.Prime) : emultiplicity p p = 1 :=
  (Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, hp.pos⟩).emultiplicity_self

theorem emultiplicity_pow_self {p n : ℕ} (hp : p.Prime) : emultiplicity p (p ^ n) = n :=
  _root_.emultiplicity_pow_self hp.ne_zero hp.prime.not_unit n

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
theorem emultiplicity_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → emultiplicity p n ! = (∑ i ∈ Ico 1 b, n / p ^ i : ℕ)
  | 0, b, _ => by simp [Ico, hp.emultiplicity_one]
  | n + 1, b, hb =>
    calc
      emultiplicity p (n + 1)! = emultiplicity p n ! + emultiplicity p (n + 1) := by
        rw [factorial_succ, hp.emultiplicity_mul, add_comm]
      _ = (∑ i ∈ Ico 1 b, n / p ^ i : ℕ) + #{i ∈ Ico 1 b | p ^ i ∣ n + 1} := by
        rw [emultiplicity_factorial hp ((log_mono_right <| le_succ _).trans_lt hb), ←
          emultiplicity_eq_card_pow_dvd hp.ne_one (succ_pos _) hb]
      _ = (∑ i ∈ Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) : ℕ) := by
        rw [sum_add_distrib, sum_boole]
        simp
      _ = (∑ i ∈ Ico 1 b, (n + 1) / p ^ i : ℕ) :=
        congr_arg _ <| Finset.sum_congr rfl fun _ _ => Nat.succ_div.symm

/-- For a prime number `p`, taking `(p - 1)` times the multiplicity of `p` in `n!` equals `n` minus
the sum of base `p` digits of `n`. -/
 theorem sub_one_mul_multiplicity_factorial {n p : ℕ} (hp : p.Prime) :
     (p - 1) * multiplicity p n ! =
     n - (p.digits n).sum := by
  simp only [multiplicity_eq_of_emultiplicity_eq_some <|
      emultiplicity_factorial hp <| lt_succ_of_lt <| lt.base (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range, ←
    sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

/-- The multiplicity of `p` in `(p * (n + 1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
theorem emultiplicity_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    emultiplicity p (p * (n + 1))! = emultiplicity p (p * n)! + emultiplicity p (n + 1) + 1 := by
  have hp' := hp.prime
  have h0 : 2 ≤ p := hp.two_le
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 ≤ p * (n + 1) := by linarith
  have h3 : p * n + 1 ≤ p * (n + 1) + 1 := by omega
  have hm : emultiplicity p (p * n)! ≠ ⊤ := by
    rw [Ne, emultiplicity_eq_top, Classical.not_not, Nat.finiteMultiplicity_iff]
    exact ⟨hp.ne_one, factorial_pos _⟩
  revert hm
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), emultiplicity p m = 0 := by
    intro m hm
    rw [emultiplicity_eq_zero, not_dvd_iff_between_consec_multiples _ hp.pos]
    rw [mem_Ico] at hm
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩
  simp_rw [← prod_Ico_id_eq_factorial, Finset.emultiplicity_prod hp', ← sum_Ico_consecutive _ h1 h3,
    add_assoc]
  intro h
  rw [WithTop.add_left_inj h, sum_Ico_succ_top h2, hp.emultiplicity_mul, hp.emultiplicity_self,
    sum_congr rfl h4, sum_const_zero, zero_add, add_comm 1]

/-- The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`. -/
theorem emultiplicity_factorial_mul {n p : ℕ} (hp : p.Prime) :
    emultiplicity p (p * n)! = emultiplicity p n ! + n := by
  induction' n with n ih
  · simp
  · simp only [hp, emultiplicity_factorial_mul_succ, ih, factorial_succ, emultiplicity_mul,
    cast_add, cast_one, ← add_assoc]
    congr 1
    rw [add_comm, add_assoc]

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater than `log p n` -/
theorem pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.Prime) (hbn : log p n < b) :
    p ^ r ∣ n ! ↔ r ≤ ∑ i ∈ Ico 1 b, n / p ^ i := by
  rw [← WithTop.coe_le_coe, ENat.some_eq_coe, ← hp.emultiplicity_factorial hbn,
    pow_dvd_iff_le_emultiplicity]

theorem emultiplicity_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) :
    emultiplicity p n ! ≤ (n / (p - 1) : ℕ) := by
  rw [hp.emultiplicity_factorial (lt_succ_self _)]
  apply WithTop.coe_mono
  exact Nat.geom_sum_Ico_le hp.two_le _ _

theorem multiplicity_choose_aux {p n b k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Ico 1 b, n / p ^ i =
      ((∑ i ∈ Finset.Ico 1 b, k / p ^ i) + ∑ i ∈ Finset.Ico 1 b, (n - k) / p ^ i) +
        #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} :=
  calc
    ∑ i ∈ Finset.Ico 1 b, n / p ^ i = ∑ i ∈ Finset.Ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [add_tsub_cancel_of_le hkn]
    _ = ∑ i ∈ Finset.Ico 1 b,
          (k / p ^ i + (n - k) / p ^ i + if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0) := by
      simp only [Nat.add_div (pow_pos hp.pos _)]
    _ = _ := by simp [sum_add_distrib, sum_boole]

/-- The multiplicity of `p` in `choose (n + k) k` is the number of carries when `k` and `n`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p (n + k)`. -/
theorem emultiplicity_choose' {p n k b : ℕ} (hp : p.Prime) (hnb : log p (n + k) < b) :
    emultiplicity p (choose (n + k) k) = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  have h₁ :
      emultiplicity p (choose (n + k) k) + emultiplicity p (k ! * n !) =
        #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} + emultiplicity p (k ! * n !) := by
    rw [← hp.emultiplicity_mul, ← mul_assoc]
    have := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [this, hp.emultiplicity_factorial hnb, hp.emultiplicity_mul,
      hp.emultiplicity_factorial ((log_mono_right (le_add_left k n)).trans_lt hnb),
      hp.emultiplicity_factorial ((log_mono_right (le_add_left n k)).trans_lt
      (add_comm n k ▸ hnb)), multiplicity_choose_aux hp (le_add_left k n)]
    simp [add_comm]
  refine WithTop.add_right_cancel ?_ h₁
  apply finiteMultiplicity_iff_emultiplicity_ne_top.1
  exact Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, mul_pos (factorial_pos k) (factorial_pos n)⟩

/-- The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
theorem emultiplicity_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
    emultiplicity p (choose n k) = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
  have := Nat.sub_add_cancel hkn
  convert @emultiplicity_choose' p (n - k) k b hp _
  · rw [this]
  exact this.symm ▸ hnb

/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
theorem emultiplicity_le_emultiplicity_choose_add {p : ℕ} (hp : p.Prime) :
    ∀ n k : ℕ, emultiplicity p n ≤ emultiplicity p (choose n k) + emultiplicity p k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
    rw [← hp.emultiplicity_mul]
    refine emultiplicity_le_emultiplicity_of_dvd_right ?_
    rw [← succ_mul_choose_eq]
    exact dvd_mul_right _ _

variable {p n k : ℕ}

theorem emultiplicity_choose_prime_pow_add_emultiplicity (hp : p.Prime) (hkn : k ≤ p ^ n)
    (hk0 : k ≠ 0) : emultiplicity p (choose (p ^ n) k) + emultiplicity p k = n :=
  le_antisymm
    (by
      have hdisj :
        Disjoint {i ∈ Ico 1 n.succ | p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i}
          {i ∈ Ico 1 n.succ | p ^ i ∣ k} := by
        simp +contextual [disjoint_right, *, dvd_iff_mod_eq_zero,
          Nat.mod_lt _ (pow_pos hp.pos _)]
      rw [emultiplicity_choose hp hkn (lt_succ_self _),
        emultiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) hk0.bot_lt
          (lt_succ_of_le (log_mono_right hkn)),
        ← Nat.cast_add]
      apply WithTop.coe_mono
      rw [log_pow hp.one_lt, ← card_union_of_disjoint hdisj, filter_union_right]
      have filter_le_Ico := (Ico 1 n.succ).card_filter_le
        fun x => p ^ x ≤ k % p ^ x + (p ^ n - k) % p ^ x ∨ p ^ x ∣ k
      rwa [card_Ico 1 n.succ] at filter_le_Ico)
    (by rw [← hp.emultiplicity_pow_self]; exact emultiplicity_le_emultiplicity_choose_add hp _ _)

theorem emultiplicity_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    emultiplicity p (choose (p ^ n) k) = ↑(n - multiplicity p k) := by
  push_cast
  rw [← emultiplicity_choose_prime_pow_add_emultiplicity hp hkn hk0,
    (finiteMultiplicity_iff.2 ⟨hp.ne_one, Nat.pos_of_ne_zero hk0⟩).emultiplicity_eq_multiplicity,
    (finiteMultiplicity_iff.2 ⟨hp.ne_one, choose_pos hkn⟩).emultiplicity_eq_multiplicity]
  norm_cast
  rw [Nat.add_sub_cancel_right]

theorem dvd_choose_pow (hp : Prime p) (hk : k ≠ 0) (hkp : k ≠ p ^ n) : p ∣ (p ^ n).choose k := by
  obtain hkp | hkp := hkp.symm.lt_or_lt
  · simp [choose_eq_zero_of_lt hkp]
  refine emultiplicity_ne_zero.1 fun h => hkp.not_le <| Nat.le_of_dvd hk.bot_lt ?_
  have H := hp.emultiplicity_choose_prime_pow_add_emultiplicity hkp.le hk
  rw [h, zero_add, emultiplicity_eq_coe] at H
  exact H.1

theorem dvd_choose_pow_iff (hp : Prime p) : p ∣ (p ^ n).choose k ↔ k ≠ 0 ∧ k ≠ p ^ n := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => dvd_choose_pow hp h.1 h.2⟩ <;> rintro rfl <;>
    simp [hp.ne_one] at h

end Prime

theorem emultiplicity_two_factorial_lt : ∀ {n : ℕ} (_ : n ≠ 0), emultiplicity 2 n ! < n := by
  have h2 := prime_two.prime
  refine binaryRec ?_ ?_
  · exact fun h => False.elim <| h rfl
  · intro b n ih h
    by_cases hn : n = 0
    · subst hn
      simp only [ne_eq, bit_eq_zero_iff, true_and, Bool.not_eq_false] at h
      simp only [bit, h, cond_true, mul_zero, zero_add, factorial_one]
      rw [Prime.emultiplicity_one]
      · exact zero_lt_one
      · decide
    have : emultiplicity 2 (2 * n)! < (2 * n : ℕ) := by
      rw [prime_two.emultiplicity_factorial_mul]
      rw [two_mul]
      push_cast
      apply WithTop.add_lt_add_right _ (ih hn)
      exact Ne.symm nofun
    cases b
    · simpa
    · suffices emultiplicity 2 (2 * n + 1) + emultiplicity 2 (2 * n)! < ↑(2 * n) + 1 by
        simpa [emultiplicity_mul, h2, prime_two, bit, factorial]
      rw [emultiplicity_eq_zero.2 (two_not_dvd_two_mul_add_one n), zero_add]
      refine this.trans ?_
      exact mod_cast lt_succ_self _

end Nat
