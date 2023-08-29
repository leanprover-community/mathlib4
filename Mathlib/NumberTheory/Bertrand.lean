/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.PrimeNormNum
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

#align_import number_theory.bertrand from "leanprover-community/mathlib"@"a16665637b378379689c566204817ae792ac8b39"

/-!
# Bertrand's Postulate

This file contains a proof of Bertrand's postulate: That between any positive number and its
double there is a prime.

The proof follows the outline of the Erdős proof presented in "Proofs from THE BOOK": One considers
the prime factorization of `(2 * n).choose n`, and splits the constituent primes up into various
groups, then upper bounds the contribution of each group. This upper bounds the central binomial
coefficient, and if the postulate does not hold, this upper bound conflicts with a simple lower
bound for large enough `n`. This proves the result holds for large enough `n`, and for smaller `n`
an explicit list of primes is provided which covers the remaining cases.

As in the [Metamath implementation](carneiro2015arithmetic), we rely on some optimizations from
[Shigenori Tochiori](tochiori_bertrand). In particular we use the cleaner bound on the central
binomial coefficient given in `Nat.four_pow_lt_mul_centralBinom`.

## References

* [M. Aigner and G. M. Ziegler _Proofs from THE BOOK_][aigner1999proofs]
* [S. Tochiori, _Considering the Proof of “There is a Prime between n and 2n”_][tochiori_bertrand]
* [M. Carneiro, _Arithmetic in Metamath, Case Study: Bertrand's Postulate_][carneiro2015arithmetic]

## Tags

Bertrand, prime, binomial coefficients
-/


open scoped BigOperators

section Real

open Real

namespace Bertrand

/-- A reified version of the `Bertrand.main_inequality` below.
This is not best possible: it actually holds for 464 ≤ x.
-/
theorem real_main_inequality {x : ℝ} (n_large : (512 : ℝ) ≤ x) :
    x * (2 * x) ^ sqrt (2 * x) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by
  let f : ℝ → ℝ := fun x => log x + sqrt (2 * x) * log (2 * x) - log 4 / 3 * x
  -- ⊢ x * (2 * x) ^ sqrt (2 * x) * 4 ^ (2 * x / 3) ≤ 4 ^ x
  have hf' : ∀ x, 0 < x → 0 < x * (2 * x) ^ sqrt (2 * x) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : ∀ x, 0 < x → f x = log (x * (2 * x) ^ sqrt (2 * x) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' ℝ) h5
    have h7 := rpow_pos_of_pos h6 (sqrt (2 * x))
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne', log_mul h5.ne' h7.ne',
      log_rpow h6, log_rpow zero_lt_four, ← mul_div_right_comm, ← mul_div, mul_comm x]
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) n_large
  -- ⊢ x * (2 * x) ^ sqrt (2 * x) * 4 ^ (2 * x / 3) ≤ 4 ^ x
  rw [← div_le_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div, ← rpow_sub four_pos, ←
    mul_div 2 x, mul_div_left_comm, ← mul_one_sub, (by norm_num1 : (1 : ℝ) - 2 / 3 = 1 / 3),
    mul_one_div, ← log_nonpos_iff (hf' x h5), ← hf x h5]
  -- porting note: the proof was rewritten, because it was too slow
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    apply ConcaveOn.add
    exact strictConcaveOn_log_Ioi.concaveOn.subset
      (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
    convert ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
      ((2 : ℝ) • LinearMap.id))) using 1
    · ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_left (two_pos)]
      norm_num1
      rfl
    apply ConvexOn.smul
    refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    exact convexOn_id (convex_Ioi (0.5 : ℝ))
  suffices ∃ x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 ≤ x ∧ 0 ≤ f x1 ∧ f x2 ≤ 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine' ⟨18, 512, by norm_num1, by norm_num1, n_large, _, _⟩
  -- ⊢ 0 ≤ f 18
  · have : sqrt (2 * 18) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    -- ⊢ 0 ≤ f 18
    rw [hf, log_nonneg_iff, this]
    rw [one_le_div] <;> norm_num1
    -- ⊢ 4 ^ (18 / 3) ≤ 18 * (2 * 18) ^ 6
                        -- ⊢ 4 ^ 6 ≤ 18 * 36 ^ 6
                        -- ⊢ 0 < 4 ^ 6
    apply le_trans _ (le_mul_of_one_le_left _ _) <;> norm_num1
                                                     -- ⊢ 4 ^ 6 ≤ 36 ^ 6
                                                     -- ⊢ 0 ≤ 36 ^ 6
                                                     -- 🎉 no goals
    apply Real.rpow_le_rpow <;> norm_num1
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
    apply rpow_nonneg_of_nonneg; norm_num1
    apply rpow_pos_of_pos; norm_num1
                           -- ⊢ 0 < 18 * (2 * 18) ^ sqrt (2 * 18) / 4 ^ (18 / 3)
    apply hf' 18; norm_num1
    -- ⊢ 0 < 18
                  -- ⊢ 0 < 18
    norm_num1
    -- 🎉 no goals
  · have : sqrt (2 * 512) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf, log_nonpos_iff (hf' _ _), this, div_le_one] <;> norm_num1
                                                            -- ⊢ 512 * 1024 ^ 32 ≤ 4 ^ (512 / 3)
                                                            -- ⊢ 0 < 4 ^ (512 / 3)
                                                            -- 🎉 no goals
                                                            -- 🎉 no goals
    have : (512 : ℝ) = 2 ^ (9 : ℕ)
    · rw [rpow_nat_cast 2 9]; norm_num1
      -- ⊢ 512 = 2 ^ 9
                              -- 🎉 no goals
    conv_lhs => rw [this]
    -- ⊢ 2 ^ ↑9 * 1024 ^ 32 ≤ 4 ^ (512 / 3)
    have : (1024 : ℝ) = 2 ^ (10 : ℕ)
    · rw [rpow_nat_cast 2 10]; norm_num1
      -- ⊢ 1024 = 2 ^ 10
                               -- 🎉 no goals
    rw [this, ← rpow_mul, ← rpow_add] <;> norm_num1
                                          -- ⊢ 2 ^ 329 ≤ 4 ^ (512 / 3)
                                          -- 🎉 no goals
                                          -- 🎉 no goals
    have : (4 : ℝ) = 2 ^ (2 : ℕ)
    · rw [rpow_nat_cast 2 2]; norm_num1
      -- ⊢ 4 = 2 ^ 2
                              -- 🎉 no goals
    rw [this, ← rpow_mul] <;> norm_num1
    -- ⊢ 2 ^ 329 ≤ 2 ^ (↑2 * (512 / 3))
                              -- ⊢ 2 ^ 329 ≤ 2 ^ (1024 / 3)
                              -- 🎉 no goals
    apply rpow_le_rpow_of_exponent_le <;> norm_num1
    -- ⊢ 1 ≤ 2
                                          -- 🎉 no goals
                                          -- 🎉 no goals
    apply rpow_pos_of_pos four_pos
    -- 🎉 no goals
 #align bertrand.real_main_inequality Bertrand.real_main_inequality

end Bertrand

end Real

section Nat

open Nat

/-- The inequality which contradicts Bertrand's postulate, for large enough `n`.
-/
theorem bertrand_main_inequality {n : ℕ} (n_large : 512 ≤ n) :
    n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
  rw [← @cast_le ℝ]
  -- ⊢ ↑(n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3)) ≤ ↑(4 ^ n)
  simp only [cast_add, cast_one, cast_mul, cast_pow, ← Real.rpow_nat_cast]
  -- ⊢ ↑n * (↑2 * ↑n) ^ ↑(sqrt (2 * n)) * ↑4 ^ ↑(2 * n / 3) ≤ ↑4 ^ ↑n
  have n_pos : 0 < n := (by decide : 0 < 512).trans_le n_large
  -- ⊢ ↑n * (↑2 * ↑n) ^ ↑(sqrt (2 * n)) * ↑4 ^ ↑(2 * n / 3) ≤ ↑4 ^ ↑n
  have n2_pos : 1 ≤ 2 * n := mul_pos (by decide) n_pos
  -- ⊢ ↑n * (↑2 * ↑n) ^ ↑(sqrt (2 * n)) * ↑4 ^ ↑(2 * n / 3) ≤ ↑4 ^ ↑n
  refine' _root_.trans (mul_le_mul _ _ _ _)
      (Bertrand.real_main_inequality (by exact_mod_cast n_large))
  · refine' mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    -- ⊢ (↑2 * ↑n) ^ ↑(sqrt (2 * n)) ≤ (2 * ↑n) ^ Real.sqrt (2 * ↑n)
    refine' Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n2_pos) _
    -- ⊢ ↑(sqrt (2 * n)) ≤ Real.sqrt (2 * ↑n)
    exact_mod_cast Real.nat_sqrt_le_real_sqrt
    -- 🎉 no goals
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num1) (cast_div_le.trans (by norm_cast))
    -- 🎉 no goals
  · exact Real.rpow_nonneg_of_nonneg (by norm_num1) _
    -- 🎉 no goals
  · refine' mul_nonneg (Nat.cast_nonneg _) _
    -- ⊢ 0 ≤ (2 * ↑n) ^ Real.sqrt (2 * ↑n)
    exact Real.rpow_nonneg_of_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) _
    -- 🎉 no goals
#align bertrand_main_inequality bertrand_main_inequality

/-- A lemma that tells us that, in the case where Bertrand's postulate does not hold, the prime
factorization of the central binomial coefficent only has factors at most `2 * n / 3 + 1`.
-/
theorem centralBinom_factorization_small (n : ℕ) (n_large : 2 < n)
    (no_prime : ¬∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n) :
    centralBinom n = ∏ p in Finset.range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p := by
  refine' (Eq.trans _ n.prod_pow_factorization_centralBinom).symm
  -- ⊢ ∏ p in Finset.range (2 * n / 3 + 1), p ^ ↑(Nat.factorization (centralBinom n …
  apply Finset.prod_subset
  -- ⊢ Finset.range (2 * n / 3 + 1) ⊆ Finset.range (2 * n + 1)
  · exact Finset.range_subset.2 (add_le_add_right (Nat.div_le_self _ _) _)
    -- 🎉 no goals
  intro x hx h2x
  -- ⊢ x ^ ↑(Nat.factorization (centralBinom n)) x = 1
  rw [Finset.mem_range, lt_succ_iff] at hx h2x
  -- ⊢ x ^ ↑(Nat.factorization (centralBinom n)) x = 1
  rw [not_le, div_lt_iff_lt_mul' three_pos, mul_comm x] at h2x
  -- ⊢ x ^ ↑(Nat.factorization (centralBinom n)) x = 1
  replace no_prime := not_exists.mp no_prime x
  -- ⊢ x ^ ↑(Nat.factorization (centralBinom n)) x = 1
  rw [← and_assoc, not_and', not_and_or, not_lt] at no_prime
  -- ⊢ x ^ ↑(Nat.factorization (centralBinom n)) x = 1
  cases' no_prime hx with h h
  -- ⊢ x ^ ↑(Nat.factorization (centralBinom n)) x = 1
  · rw [factorization_eq_zero_of_non_prime n.centralBinom h, Nat.pow_zero]
    -- 🎉 no goals
  · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h h2x, Nat.pow_zero]
    -- 🎉 no goals
#align central_binom_factorization_small centralBinom_factorization_small

/-- An upper bound on the central binomial coefficient used in the proof of Bertrand's postulate.
The bound splits the prime factors of `centralBinom n` into those
1. At most `sqrt (2 * n)`, which contribute at most `2 * n` for each such prime.
2. Between `sqrt (2 * n)` and `2 * n / 3`, which contribute at most `4^(2 * n / 3)` in total.
3. Between `2 * n / 3` and `n`, which do not exist.
4. Between `n` and `2 * n`, which would not exist in the case where Bertrand's postulate is false.
5. Above `2 * n`, which do not exist.
-/
theorem centralBinom_le_of_no_bertrand_prime (n : ℕ) (n_big : 2 < n)
    (no_prime : ¬∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_big
  -- ⊢ centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3)
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  -- ⊢ centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3)
  let S := (Finset.range (2 * n / 3 + 1)).filter Nat.Prime
  -- ⊢ centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3)
  let f x := x ^ n.centralBinom.factorization x
  -- ⊢ centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3)
  have : ∏ x : ℕ in S, f x = ∏ x : ℕ in Finset.range (2 * n / 3 + 1), f x := by
    refine' Finset.prod_filter_of_ne fun p _ h => _
    contrapose! h; dsimp only
    rw [factorization_eq_zero_of_non_prime n.centralBinom h, _root_.pow_zero]
  rw [centralBinom_factorization_small n n_big no_prime, ← this, ←
    Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
  apply mul_le_mul'
  -- ⊢ ∏ x in Finset.filter (fun x => x ≤ sqrt (2 * n)) S, f x ≤ (2 * n) ^ sqrt (2  …
  · refine' (Finset.prod_le_prod' fun p _ => (_ : f p ≤ 2 * n)).trans _
    -- ⊢ f p ≤ 2 * n
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
      -- 🎉 no goals
    have : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by rw [card_Icc, Nat.add_sub_cancel]
    -- ⊢ ∏ i in Finset.filter (fun x => x ≤ sqrt (2 * n)) S, 2 * n ≤ (2 * n) ^ sqrt ( …
    rw [Finset.prod_const]
    -- ⊢ (2 * n) ^ Finset.card (Finset.filter (fun x => x ≤ sqrt (2 * n)) S) ≤ (2 * n …
    refine' pow_le_pow n2_pos ((Finset.card_le_of_subset fun x hx => _).trans this.le)
    -- ⊢ x ∈ Finset.Icc 1 (sqrt (2 * n))
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    -- ⊢ x ∈ Finset.Icc 1 (sqrt (2 * n))
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    -- 🎉 no goals
  · refine' le_trans _ (primorial_le_4_pow (2 * n / 3))
    -- ⊢ ∏ x in Finset.filter (fun x => ¬x ≤ sqrt (2 * n)) S, f x ≤ primorial (2 * n  …
    refine' (Finset.prod_le_prod' fun p hp => (_ : f p ≤ p)).trans _
    -- ⊢ f p ≤ p
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      -- ⊢ f p ≤ p
      refine' (pow_le_pow (Finset.mem_filter.1 h1).2.one_lt.le _).trans (pow_one p).le
      -- ⊢ ↑(Nat.factorization (centralBinom n)) p ≤ 1
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
      -- 🎉 no goals
    refine' Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) _
    -- ⊢ ∀ (i : ℕ), i ∈ Finset.filter Nat.Prime (Finset.range (2 * n / 3 + 1)) → ¬i ∈ …
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
    -- 🎉 no goals
#align central_binom_le_of_no_bertrand_prime centralBinom_le_of_no_bertrand_prime

namespace Nat

/-- Proves that Bertrand's postulate holds for all sufficiently large `n`.
-/
theorem exists_prime_lt_and_le_two_mul_eventually (n : ℕ) (n_big : 512 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  -- Assume there is no prime in the range.
  by_contra no_prime
  -- ⊢ False
  -- Then we have the above sub-exponential bound on the size of this central binomial coefficient.
  -- We now couple this bound with an exponential lower bound on the central binomial coefficient,
  -- yielding an inequality which we have seen is false for large enough n.
  have H1 : n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) ≤ 4 ^ n := bertrand_main_inequality n_big
  -- ⊢ False
  have H2 : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n (le_trans (by norm_num1) n_big)
  have H3 : n.centralBinom ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) :=
    centralBinom_le_of_no_bertrand_prime n (lt_of_lt_of_le (by norm_num1) n_big) no_prime
  rw [mul_assoc] at H1; exact not_le.2 H2 ((mul_le_mul_left' H3 n).trans H1)
  -- ⊢ False
                        -- 🎉 no goals
#align nat.exists_prime_lt_and_le_two_mul_eventually Nat.exists_prime_lt_and_le_two_mul_eventually

/-- Proves that Bertrand's postulate holds over all positive naturals less than n by identifying a
descending list of primes, each no more than twice the next, such that the list contains a witness
for each number ≤ n.
-/
theorem exists_prime_lt_and_le_two_mul_succ {n} (q) {p : ℕ} (prime_p : Nat.Prime p)
    (covering : p ≤ 2 * q) (H : n < q → ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n) (hn : n < p) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  by_cases p ≤ 2 * n; · exact ⟨p, prime_p, hn, h⟩
  -- ⊢ ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n
  -- ⊢ ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n
                        -- 🎉 no goals
  exact H (lt_of_mul_lt_mul_left' (lt_of_lt_of_le (not_le.1 h) covering))
  -- 🎉 no goals
#align nat.exists_prime_lt_and_le_two_mul_succ Nat.exists_prime_lt_and_le_two_mul_succ

/--
**Bertrand's Postulate**: For any positive natural number, there is a prime which is greater than
it, but no more than twice as large.
-/
theorem exists_prime_lt_and_le_two_mul (n : ℕ) (hn0 : n ≠ 0) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
  -- Split into cases whether `n` is large or small
  cases' lt_or_le 511 n with h h
  -- ⊢ ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n
  -- If `n` is large, apply the lemma derived from the inequalities on the central binomial
  -- coefficient.
  · exact exists_prime_lt_and_le_two_mul_eventually n h
    -- 🎉 no goals
  replace h : n < 521 := h.trans_lt (by norm_num1)
  -- ⊢ ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n
  revert h
  -- ⊢ n < 521 → ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n
  -- For small `n`, supply a list of primes to cover the initial cases.
  open Lean Elab Tactic in
  run_tac do
    for i in [317, 163, 83, 43, 23, 13, 7, 5, 3, 2] do
      let i : Term := quote i
      evalTactic <| ←
        `(tactic| refine' exists_prime_lt_and_le_two_mul_succ $i (by norm_num1) (by norm_num1) _)
  exact fun h2 => ⟨2, prime_two, h2, Nat.mul_le_mul_left 2 (Nat.pos_of_ne_zero hn0)⟩
#align nat.exists_prime_lt_and_le_two_mul Nat.exists_prime_lt_and_le_two_mul

alias bertrand := Nat.exists_prime_lt_and_le_two_mul
#align nat.bertrand Nat.bertrand

end Nat

end Nat
