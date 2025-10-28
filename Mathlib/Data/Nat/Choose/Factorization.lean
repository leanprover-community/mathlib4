/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Patrick Stevens, Thomas Browning
-/
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Factorization of Binomial Coefficients

This file contains a few results on the multiplicity of prime factors within certain size
bounds in binomial coefficients. These include:

* `Nat.factorization_choose_le_log`: a logarithmic upper bound on the multiplicity of a prime in
  a binomial coefficient.
* `Nat.factorization_choose_le_one`: Primes above `sqrt n` appear at most once
  in the factorization of `n` choose `k`.
* `Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul`: Primes from `2 * n / 3` to `n`
  do not appear in the factorization of the `n`th central binomial coefficient.
* `Nat.factorization_choose_eq_zero_of_lt`: Primes greater than `n` do not
  appear in the factorization of `n` choose `k`.

These results appear in the [Erdős proof of Bertrand's postulate](aigner1999proofs).
-/

open Finset List Finsupp

namespace Nat
variable {a b c : ℕ}

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
theorem factorization_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → (n)!.factorization p = ∑ i ∈ Ico 1 b, n / p ^ i
  | 0, b, _ => by simp
  | n + 1, b, hb =>
    calc
      (n + 1)!.factorization p = (n + 1).factorization p + (n)!.factorization p := by
        rw [factorial_succ, factorization_mul (zero_ne_add_one n).symm n.factorial_ne_zero,
          coe_add, Pi.add_apply]
      _ = #{i ∈ Ico 1 b | p ^ i ∣ n + 1} + ∑ i ∈ Ico 1 b, n / p ^ i := by
        rw [factorization_factorial hp ((log_mono_right <| le_succ _).trans_lt hb), add_left_inj]
        apply factorization_eq_card_pow_dvd_of_lt hp (zero_lt_succ n)
          (lt_pow_of_log_lt hp.one_lt hb)
      _ = ∑ i ∈ Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) := by
        simp [Nat.add_comm, sum_add_distrib, sum_boole]
      _ = ∑ i ∈ Ico 1 b, (n + 1) / p ^ i := Finset.sum_congr rfl fun _ _ => Nat.succ_div.symm

/-- For a prime number `p`, taking `(p - 1)` times the factorization of `p` in `n!` equals `n` minus
the sum of base `p` digits of `n`. -/
theorem sub_one_mul_factorization_factorial {n p : ℕ} (hp : p.Prime) :
    (p - 1) * (n)!.factorization p = n - (p.digits n).sum := by
  simp only [factorization_factorial hp <| lt_succ_of_lt <| lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range,
    ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

/-- The factorization of `p` in `(p * (n + 1))!` is one more than the sum of the factorizations of
`p` in `(p * n)!` and `n + 1`. -/
theorem factorization_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    (p * (n + 1))!.factorization p = (p * n)!.factorization p + (n + 1).factorization p + 1 := by
  have h0 : 2 ≤ p := hp.two_le
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 ≤ p * (n + 1) := by linarith
  have h3 : p * n + 1 ≤ p * (n + 1) + 1 := by omega
  have h4 m (hm : m ∈ Ico (p * n + 1) (p * (n + 1))) : m.factorization p = 0 := by
    apply factorization_eq_zero_of_not_dvd
    exact not_dvd_of_lt_of_lt_mul_succ (mem_Ico.mp hm).left (mem_Ico.mp hm).right
  rw [← prod_Ico_id_eq_factorial, factorization_prod_apply (fun _ hx ↦ ne_zero_of_lt
    (mem_Ico.mp hx).left), ← sum_Ico_consecutive _ h1 h3, add_assoc, sum_Ico_succ_top h2,
    ← prod_Ico_id_eq_factorial, factorization_prod_apply (fun _ hx ↦ ne_zero_of_lt
    (mem_Ico.mp hx).left), factorization_mul (ne_zero_of_lt h0) (zero_ne_add_one n).symm,
    coe_add, Pi.add_apply, hp.factorization_self, sum_congr rfl h4, sum_const_zero, zero_add,
    add_comm 1]

/-- The factorization of `p` in `(p * n)!` is `n` more than that of `n!`. -/
theorem factorization_factorial_mul {n p : ℕ} (hp : p.Prime) :
    (p * n)!.factorization p = (n)!.factorization p + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [factorization_factorial_mul_succ hp, ih, factorial_succ,
      factorization_mul (zero_ne_add_one n).symm (factorial_ne_zero n)]
    ring

theorem factorization_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n)!.factorization p ≤ (n / (p - 1) : ℕ) := by
  rw [factorization_factorial hp (Nat.lt_add_one (log p n))]
  exact Nat.geom_sum_Ico_le hp.two_le _ _

lemma multiplicity_choose_aux {p n b k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
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

/-- The factorization of `p` in `choose (n + k) k` is the number of carries when `k` and `n` are
added in base `p`. The set is expressed by filtering `Ico 1 b` where `b` is any bound greater
than `log p (n + k)`. -/
theorem factorization_choose' {p n k b : ℕ} (hp : p.Prime) (hnb : log p (n + k) < b) :
    (choose (n + k) k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  have h₁ : (choose (n + k) k).factorization p +  (k ! * n !).factorization p
    = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} + (k ! * n !).factorization p := by
    have h2 := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [← Pi.add_apply, ← coe_add, ← factorization_mul (ne_of_gt <| choose_pos (le_add_left k n))
      (by positivity), ← mul_assoc, h2,
      factorization_factorial hp hnb, factorization_mul (factorial_ne_zero k) (factorial_ne_zero n),
      coe_add, Pi.add_apply, factorization_factorial hp ((log_mono_right (le_add_left k n)).trans_lt
      hnb), factorization_factorial hp ((log_mono_right (le_add_left n k)).trans_lt
      (add_comm n k ▸ hnb)), multiplicity_choose_aux hp (le_add_left k n)]
    simp only [add_tsub_cancel_right, add_comm]
  exact Nat.add_right_cancel h₁

/-- The factorization of `p` in `choose n k` is the number of carries when `k` and `n - k`
are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
is any bound greater than `log p n`. -/
theorem factorization_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
    (choose n k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
  rw [←factorization_choose' hp ((Nat.sub_add_cancel hkn).symm ▸ hnb), Nat.sub_add_cancel hkn]

/-- Modified version of `emultiplicity_le_emultiplicity_of_dvd_right`
but for factorization. -/
theorem factorization_le_factorization_of_dvd_right (h : b ∣ c) (hb : b ≠ 0) (hc : c ≠ 0) :
    b.factorization a ≤ c.factorization a := by
  obtain ⟨k, rfl⟩ := h; simp [factorization_mul hb (Nat.ne_zero_of_mul_ne_zero_right hc)]

/-- A lower bound on the factorization of `p` in `choose n k`. -/
theorem factorization_le_factorization_choose_add {p : ℕ} :
    ∀ {n k : ℕ}, k ≤ n → k ≠ 0 →
      n.factorization p ≤ (choose n k).factorization p + k.factorization p
  | n, 0, _, _ => by tauto
  | 0, x + 1, _, _ => by simp
  | n + 1, k + 1, hkn, hk => by
    rw [← Pi.add_apply, ← coe_add, ← factorization_mul (ne_of_gt <| choose_pos hkn)
      (zero_ne_add_one k).symm]
    refine factorization_le_factorization_of_dvd_right ?_ (zero_ne_add_one n).symm
      (Nat.mul_ne_zero (ne_of_gt <| choose_pos hkn) (by positivity))
    rw [← succ_mul_choose_eq]
    exact dvd_mul_right _ _

variable {p n k : ℕ}

theorem factorization_choose_prime_pow_add_factorization (hp : p.Prime) (hkn : k ≤ p ^ n)
    (hk0 : k ≠ 0) : (choose (p ^ n) k).factorization p + k.factorization p = n := by
  apply le_antisymm
  · have hdisj : Disjoint {i ∈ Ico 1 n.succ | p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i}
        {i ∈ Ico 1 n.succ | p ^ i ∣ k} := by
      simp +contextual [Finset.disjoint_right, dvd_iff_mod_eq_zero, Nat.mod_lt _ (pow_pos hp.pos _)]
    rw [factorization_choose hp hkn (lt_succ_self _), factorization_eq_card_pow_dvd_of_lt hp
      hk0.bot_lt (lt_of_le_of_lt hkn <| Nat.pow_lt_pow_succ hp.one_lt), log_pow hp.one_lt,
      ← card_union_of_disjoint hdisj, filter_union_right]
    have filter_le_Ico := (Ico 1 n.succ).card_filter_le
      fun x => p ^ x ≤ k % p ^ x + (p ^ n - k) % p ^ x ∨ p ^ x ∣ k
    rwa [card_Ico 1 n.succ] at filter_le_Ico
  · nth_rewrite 1 [← factorization_pow_self (n:=n) hp]
    exact factorization_le_factorization_choose_add hkn hk0

theorem factorization_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    (choose (p ^ n) k).factorization p = n - k.factorization p := by
  nth_rewrite 2 [← factorization_choose_prime_pow_add_factorization hp hkn hk0]
  rw [Nat.add_sub_cancel_right]

end Nat


namespace Nat

variable {p n k : ℕ}

/-- A logarithmic upper bound on the multiplicity of a prime in a binomial coefficient. -/
theorem factorization_choose_le_log : (choose n k).factorization p ≤ log p n := by
  by_cases h : (choose n k).factorization p = 0
  · simp [h]
  have hp : p.Prime := Not.imp_symm (choose n k).factorization_eq_zero_of_not_prime h
  have hkn : k ≤ n := by
    refine le_of_not_gt fun hnk => h ?_
    simp [choose_eq_zero_of_lt hnk]
  rw [factorization_choose hp hkn (Nat.lt_add_one _)]
  exact (card_filter_le ..).trans_eq (Nat.card_Ico _ _)

/-- A `pow` form of `Nat.factorization_choose_le` -/
theorem pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p ≤ n :=
  pow_le_of_le_log hn.ne' factorization_choose_le_log

/-- Primes greater than about `sqrt n` appear only to multiplicity 0 or 1
in the binomial coefficient. -/
theorem factorization_choose_le_one (p_large : n < p ^ 2) : (choose n k).factorization p ≤ 1 := by
  apply factorization_choose_le_log.trans
  rcases eq_or_ne n 0 with (rfl | hn0); · simp
  exact Nat.lt_succ_iff.1 (log_lt_of_lt_pow hn0 p_large)

theorem factorization_choose_of_lt_three_mul (hp' : p ≠ 2) (hk : p ≤ k) (hk' : p ≤ n - k)
    (hn : n < 3 * p) : (choose n k).factorization p = 0 := by
  rcases em' p.Prime with hp | hp
  · exact factorization_eq_zero_of_not_prime (choose n k) hp
  rcases lt_or_ge n k with hnk | hkn
  · simp [choose_eq_zero_of_lt hnk]
  simp only [factorization_choose hp hkn (Nat.lt_add_one _), card_eq_zero, filter_eq_empty_iff,
    mem_Ico, not_le, and_imp]
  intro i hi₁ hi
  rcases eq_or_lt_of_le hi₁ with (rfl | hi)
  · rw [pow_one, ← add_lt_add_iff_left (2 * p), ← succ_mul, two_mul, add_add_add_comm]
    exact
      lt_of_le_of_lt
        (add_le_add
          (add_le_add_right (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk)) (k % p))
          (add_le_add_right (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk'))
            ((n - k) % p)))
        (by rwa [div_add_mod, div_add_mod, add_tsub_cancel_of_le hkn])
  · replace hn : n < p ^ i := by
      have : 3 ≤ p := lt_of_le_of_ne hp.two_le hp'.symm
      calc
        n < 3 * p := hn
        _ ≤ p * p := by gcongr
        _ = p ^ 2 := (sq p).symm
        _ ≤ p ^ i := pow_right_mono₀ hp.one_lt.le hi
    rwa [mod_eq_of_lt (lt_of_le_of_lt hkn hn), mod_eq_of_lt (lt_of_le_of_lt tsub_le_self hn),
      add_tsub_cancel_of_le hkn]

/-- Primes greater than about `2 * n / 3` and less than `n` do not appear in the factorization of
`centralBinom n`. -/
theorem factorization_centralBinom_of_two_mul_self_lt_three_mul (n_big : 2 < n) (p_le_n : p ≤ n)
    (big : 2 * n < 3 * p) : (centralBinom n).factorization p = 0 := by
  refine factorization_choose_of_lt_three_mul ?_ p_le_n (p_le_n.trans ?_) big
  · cutsat
  · rw [two_mul, add_tsub_cancel_left]

theorem factorization_factorial_eq_zero_of_lt (h : n < p) : (factorial n).factorization p = 0 := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [factorial_succ, factorization_mul n.succ_ne_zero n.factorial_ne_zero, Finsupp.coe_add,
      Pi.add_apply, hn (lt_of_succ_lt h), add_zero, factorization_eq_zero_of_lt h]

theorem factorization_choose_eq_zero_of_lt (h : n < p) : (choose n k).factorization p = 0 := by
  by_cases hnk : n < k; · simp [choose_eq_zero_of_lt hnk]
  rw [choose_eq_factorial_div_factorial (le_of_not_gt hnk),
    factorization_div (factorial_mul_factorial_dvd_factorial (le_of_not_gt hnk)), Finsupp.coe_tsub,
    Pi.sub_apply, factorization_factorial_eq_zero_of_lt h, zero_tsub]

/-- If a prime `p` has positive multiplicity in the `n`th central binomial coefficient,
`p` is no more than `2 * n` -/
theorem factorization_centralBinom_eq_zero_of_two_mul_lt (h : 2 * n < p) :
    (centralBinom n).factorization p = 0 :=
  factorization_choose_eq_zero_of_lt h

/-- Contrapositive form of `Nat.factorization_centralBinom_eq_zero_of_two_mul_lt` -/
theorem le_two_mul_of_factorization_centralBinom_pos
    (h_pos : 0 < (centralBinom n).factorization p) : p ≤ 2 * n :=
  le_of_not_gt (pos_iff_ne_zero.mp h_pos ∘ factorization_centralBinom_eq_zero_of_two_mul_lt)

/-- A binomial coefficient is the product of its prime factors, which are at most `n`. -/
theorem prod_pow_factorization_choose (n k : ℕ) (hkn : k ≤ n) :
    (∏ p ∈ Finset.range (n + 1), p ^ (Nat.choose n k).factorization p) = choose n k := by
  conv_rhs => rw [← factorization_prod_pow_eq_self (choose_ne_zero hkn)]
  rw [eq_comm]
  apply Finset.prod_subset
  · intro p hp
    rw [Finset.mem_range]
    contrapose! hp
    rw [Finsupp.mem_support_iff, Classical.not_not, factorization_choose_eq_zero_of_lt hp]
  · intro p _ h2
    simp [Classical.not_not.1 (mt Finsupp.mem_support_iff.2 h2)]

/-- The `n`th central binomial coefficient is the product of its prime factors, which are
at most `2n`. -/
theorem prod_pow_factorization_centralBinom (n : ℕ) :
    (∏ p ∈ Finset.range (2 * n + 1), p ^ (centralBinom n).factorization p) = centralBinom n := by
  apply prod_pow_factorization_choose
  cutsat

end Nat
