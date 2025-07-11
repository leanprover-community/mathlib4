/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Patrick Stevens, Thomas Browning
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Multiplicity

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


namespace Nat

variable {p n k : ℕ}

/-- A logarithmic upper bound on the multiplicity of a prime in a binomial coefficient. -/
theorem factorization_choose_le_log : (choose n k).factorization p ≤ log p n := by
  by_cases h : (choose n k).factorization p = 0
  · simp [h]
  have hp : p.Prime := Not.imp_symm (choose n k).factorization_eq_zero_of_non_prime h
  have hkn : k ≤ n := by
    refine le_of_not_gt fun hnk => h ?_
    simp [choose_eq_zero_of_lt hnk]
  rw [factorization_def _ hp, @padicValNat_def _ ⟨hp⟩ _ (choose_pos hkn)]
  rw [← Nat.cast_le (α := ℕ∞), ← FiniteMultiplicity.emultiplicity_eq_multiplicity]
  · simp only [hp.emultiplicity_choose hkn (lt_add_one _), Nat.cast_le]
    exact (Finset.card_filter_le _ _).trans (le_of_eq (Nat.card_Ico _ _))
  apply Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, choose_pos hkn⟩

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
  · exact factorization_eq_zero_of_non_prime (choose n k) hp
  rcases lt_or_ge n k with hnk | hkn
  · simp [choose_eq_zero_of_lt hnk]
  rw [factorization_def _ hp, @padicValNat_def _ ⟨hp⟩ _ (choose_pos hkn),
    ← emultiplicity_eq_zero_iff_multiplicity_eq_zero]
  simp only [hp.emultiplicity_choose hkn (lt_add_one _), cast_eq_zero, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, not_le]
  intro i hi
  rcases eq_or_lt_of_le (Finset.mem_Ico.mp hi).1 with (rfl | hi)
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
        _ ≤ p * p := mul_le_mul_right' this p
        _ = p ^ 2 := (sq p).symm
        _ ≤ p ^ i := pow_right_mono₀ hp.one_lt.le hi
    rwa [mod_eq_of_lt (lt_of_le_of_lt hkn hn), mod_eq_of_lt (lt_of_le_of_lt tsub_le_self hn),
      add_tsub_cancel_of_le hkn]

/-- Primes greater than about `2 * n / 3` and less than `n` do not appear in the factorization of
`centralBinom n`. -/
theorem factorization_centralBinom_of_two_mul_self_lt_three_mul (n_big : 2 < n) (p_le_n : p ≤ n)
    (big : 2 * n < 3 * p) : (centralBinom n).factorization p = 0 := by
  refine factorization_choose_of_lt_three_mul ?_ p_le_n (p_le_n.trans ?_) big
  · omega
  · rw [two_mul, add_tsub_cancel_left]

theorem factorization_factorial_eq_zero_of_lt (h : n < p) : (factorial n).factorization p = 0 := by
  induction' n with n hn; · simp
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
  conv_rhs => rw [← factorization_prod_pow_eq_self (choose_pos hkn).ne']
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
  omega

end Nat
