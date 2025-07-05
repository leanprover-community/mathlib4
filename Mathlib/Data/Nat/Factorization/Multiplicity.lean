/-
Copyright (c) 2025 Qi Wen Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Wen Wei
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Natural number factorization

This file contains lemmas about the factorization function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.


## Factorization calculations

* `Nat.factorization_factorial`: Legendre's Theorem. The factorization of `p` in `n!` is
  `n / p + ... + n / p ^ b` for any `b` such that `n / p ^ (b + 1) = 0`. See `padicValNat_factorial`
  for this result stated in the language of `p`-adic valuations and
  `sub_one_mul_padicValNat_factorial` for a factorization result.
* `Nat.factorization_factorial_mul`: The factorization of `p` in `(p * n)!` is `n` more than
  that of `n!`.
* `Nat.factorization_choose`: Kummer's Theorem. The factorization of `p` in `n.choose k`
   is the number of carries when `k` and `n - k` are added in base `p`.
   See `padicValNat_choose` for the same result but stated in the language of `p`-adic
   valuations and `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` for a related result.

## Tags

Legendre, p-adic
-/

open Finset List Finsupp

namespace Nat
variable {a b c : ℕ}

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
theorem factorization_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → (n !).factorization p = ∑ i ∈ Ico 1 b, n / p ^ i
  | 0, b, _ => by simp
  | n + 1, b, hb =>
    calc
      ((n + 1)!).factorization p = (n + 1).factorization p + (n !).factorization p := by
        rw [factorial_succ, factorization_mul (zero_ne_add_one n).symm (factorial_ne_zero n),
          coe_add, Pi.add_apply]
      _ = #{i ∈ Ico 1 b | p ^ i ∣ n + 1} + (∑ i ∈ Ico 1 b, n / p ^ i : ℕ) := by
        rw [factorization_factorial hp ((log_mono_right <| le_succ _).trans_lt hb), add_left_inj]
        apply factorization_eq_card_pow_dvd_of_lt hp (zero_lt_succ n)
          (lt_pow_of_log_lt hp.one_lt hb)
      _ = (∑ i ∈ Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) : ℕ) := by
        simp [Nat.add_comm, sum_add_distrib, sum_boole]
      _ = (∑ i ∈ Ico 1 b, (n + 1) / p ^ i : ℕ) :=
        Finset.sum_congr rfl fun _ _ => Nat.succ_div.symm

/-- For a prime number `p`, taking `(p - 1)` times the factorization of `p` in `n!` equals `n` minus
the sum of base `p` digits of `n`. -/
theorem sub_one_mul_factorization_factorial {n p : ℕ} (hp : p.Prime) :
    (p - 1) * (n !).factorization p = n - (p.digits n).sum := by
  simp only [factorization_factorial hp <| lt_succ_of_lt <| lt.base (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range, ←
    sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

/-- The factorization of `p` in `(p * (n + 1))!` is one more than the sum of the factorizations of
`p` in `(p * n)!` and `n + 1`. -/
theorem factorization_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    ((p * (n + 1))!).factorization p =
    ((p * n)!).factorization p + (n + 1).factorization p + 1 := by
  have h0 : 2 ≤ p := hp.two_le
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 ≤ p * (n + 1) := by linarith
  have h3 : p * n + 1 ≤ p * (n + 1) + 1 := by omega
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), m.factorization p = 0 := by
    intro m hm
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
    ((p * n)!).factorization p = (n !).factorization p + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [factorization_factorial_mul_succ hp, ih, factorial_succ,
      factorization_mul (zero_ne_add_one n).symm (factorial_ne_zero n)]
    ring

theorem factorization_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n !).factorization p ≤ (n / (p - 1) : ℕ) := by
  rw [factorization_factorial hp (Nat.lt_add_one (log p n))]
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


/-- The factorization of `p` in `choose (n + k) k` is the number of carries when `k` and `n` are
added in base `p`. The set is expressed by filtering `Ico 1 b` where `b` is any bound greater
than `log p (n + k)`. -/
theorem factorization_choose' {p n k b : ℕ} (hp : p.Prime) (hnb : log p (n + k) < b) :
    (choose (n + k) k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  have h₁ : (choose (n + k) k).factorization p +  (k ! * n !).factorization p
    = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} + (k ! * n !).factorization p := by
    have h2 := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [← Pi.add_apply, ← coe_add, ← factorization_mul (ne_of_gt <| choose_pos (le_add_left k n))
      (Nat.mul_ne_zero (factorial_ne_zero k) (factorial_ne_zero n)), ← mul_assoc, h2,
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
  rcases h with ⟨k, rfl⟩
  simp [factorization_mul hb (Nat.ne_zero_of_mul_ne_zero_right hc)]

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
      (Nat.mul_ne_zero (ne_of_gt <| choose_pos hkn) (zero_ne_add_one k).symm)
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
