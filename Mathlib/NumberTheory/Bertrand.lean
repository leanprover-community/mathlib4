/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Tactic.NormNum.Prime

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


section Real

open Real

namespace Bertrand

/-- A refined version of the `Bertrand.main_inequality` below.
This is not best possible: it actually holds for 464 ≤ x.
-/
theorem real_main_inequality {x : ℝ} (x_large : (512 : ℝ) ≤ x) :
    x * (2 * x) ^ √(2 * x) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by
  let f : ℝ → ℝ := fun x => log x + √(2 * x) * log (2 * x) - log 4 / 3 * x
  have hf' : ∀ x, 0 < x → 0 < x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : ∀ x, 0 < x → f x = log (x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' ℝ) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x))
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne', log_mul h5.ne' h7.ne',
      log_rpow h6, log_rpow zero_lt_four, ← mul_div_right_comm, ← mul_div, mul_comm x]
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div, ← rpow_sub four_pos, ←
    mul_div 2 x, mul_div_left_comm, ← mul_one_sub, (by norm_num1 : (1 : ℝ) - 2 / 3 = 1 / 3),
    mul_one_div, ← log_nonpos_iff (hf' x h5).le, ← hf x h5]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): the proof was rewritten, because it was too slow
  -- Original:
  /-
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    refine ((strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ioi_subset_Ioi _)
      (convex_Ioi 0.5)).add ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
      ((2 : ℝ) • LinearMap.id)).subset
      (fun a ha => lt_of_eq_of_lt _ ((mul_lt_mul_left two_pos).mpr ha)) (convex_Ioi 0.5))).sub
      ((convex_on_id (convex_Ioi (0.5 : ℝ))).smul (div_nonneg (log_nonneg _) _))
    norm_num
  -/
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · exact strictConcaveOn_log_Ioi.concaveOn.subset
          (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
      convert ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
        ((2 : ℝ) • LinearMap.id))) using 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_left (two_pos)]
      norm_num1
      rfl
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : ℝ))
  suffices ∃ x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 ≤ x ∧ 0 ≤ f x1 ∧ f x2 ≤ 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have : √(2 * 18 : ℝ) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonneg_iff (by positivity), this, one_le_div (by norm_num1)]
    norm_num1
  · have : √(2 * 512) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonpos_iff (hf' _ (by norm_num1)).le, this,
        div_le_one (by positivity)]
    conv in 512 => equals 2 ^ 9 => norm_num1
    conv in 2 * 512 => equals 2 ^ 10 => norm_num1
    conv in 32 => rw [← Nat.cast_ofNat]
    rw [rpow_natCast, ← pow_mul, ← pow_add]
    conv in 4 => equals 2 ^ (2 : ℝ) => rw [rpow_two]; norm_num1
    rw [← rpow_mul, ← rpow_natCast]
    on_goal 1 => apply rpow_le_rpow_of_exponent_le
    all_goals norm_num1

end Bertrand

end Real

section Nat

open Nat

/-- The inequality which contradicts Bertrand's postulate, for large enough `n`.
-/
theorem bertrand_main_inequality {n : ℕ} (n_large : 512 ≤ n) :
    n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
  rw [← @cast_le ℝ]
  simp only [cast_mul, cast_pow, ← Real.rpow_natCast, cast_ofNat]
  refine _root_.trans ?_ (Bertrand.real_main_inequality (by exact_mod_cast n_large))
  gcongr
  · have n2_pos : 0 < 2 * n := by positivity
    exact mod_cast n2_pos
  · exact_mod_cast Real.nat_sqrt_le_real_sqrt
  · norm_num1
  · exact cast_div_le.trans (by norm_cast)

/-- A lemma that tells us that, in the case where Bertrand's postulate does not hold, the prime
factorization of the central binomial coefficient only has factors at most `2 * n / 3 + 1`.
-/
theorem centralBinom_factorization_small (n : ℕ) (n_large : 2 < n)
    (no_prime : ¬∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n) :
    centralBinom n = ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p := by
  refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
  apply Finset.prod_subset
  · exact Finset.range_subset_range.2 (add_le_add_right (Nat.div_le_self _ _) _)
  intro x hx h2x
  rw [Finset.mem_range, Nat.lt_succ_iff] at hx h2x
  rw [not_le, div_lt_iff_lt_mul three_pos, mul_comm x] at h2x
  replace no_prime := not_exists.mp no_prime x
  rw [← and_assoc, not_and', not_and_or, not_lt] at no_prime
  rcases no_prime hx with h | h
  · rw [factorization_eq_zero_of_non_prime n.centralBinom h, Nat.pow_zero]
  · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h h2x, Nat.pow_zero]

/-- An upper bound on the central binomial coefficient used in the proof of Bertrand's postulate.
The bound splits the prime factors of `centralBinom n` into those
1. At most `sqrt (2 * n)`, which contribute at most `2 * n` for each such prime.
2. Between `sqrt (2 * n)` and `2 * n / 3`, which contribute at most `4^(2 * n / 3)` in total.
3. Between `2 * n / 3` and `n`, which do not exist.
4. Between `n` and `2 * n`, which would not exist in the case where Bertrand's postulate is false.
5. Above `2 * n`, which do not exist.
-/
theorem centralBinom_le_of_no_bertrand_prime (n : ℕ) (n_large : 2 < n)
    (no_prime : ¬∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose! h; dsimp only [f]
    rw [factorization_eq_zero_of_non_prime n.centralBinom h, _root_.pow_zero]
  rw [centralBinom_factorization_small n n_large no_prime, ← this, ←
    Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_4_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

namespace Nat

/-- Proves that **Bertrand's postulate** holds for all sufficiently large `n`.
-/
theorem exists_prime_lt_and_le_two_mul_eventually (n : ℕ) (n_large : 512 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  -- Assume there is no prime in the range.
  by_contra no_prime
  -- Then we have the above sub-exponential bound on the size of this central binomial coefficient.
  -- We now couple this bound with an exponential lower bound on the central binomial coefficient,
  -- yielding an inequality which we have seen is false for large enough n.
  have H1 : n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) ≤ 4 ^ n := bertrand_main_inequality n_large
  have H2 : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n (le_trans (by norm_num1) n_large)
  have H3 : n.centralBinom ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) :=
    centralBinom_le_of_no_bertrand_prime n (lt_of_lt_of_le (by norm_num1) n_large) no_prime
  rw [mul_assoc] at H1; exact not_le.2 H2 ((mul_le_mul_left' H3 n).trans H1)

/-- Proves that Bertrand's postulate holds over all positive naturals less than n by identifying a
descending list of primes, each no more than twice the next, such that the list contains a witness
for each number ≤ n.
-/
theorem exists_prime_lt_and_le_two_mul_succ {n} (q) {p : ℕ} (prime_p : Nat.Prime p)
    (covering : p ≤ 2 * q) (H : n < q → ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n) (hn : n < p) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  by_cases h : p ≤ 2 * n; · exact ⟨p, prime_p, hn, h⟩
  exact H (lt_of_mul_lt_mul_left' (lt_of_lt_of_le (not_le.1 h) covering))

/--
**Bertrand's Postulate**: For any positive natural number, there is a prime which is greater than
it, but no more than twice as large.
-/
theorem exists_prime_lt_and_le_two_mul (n : ℕ) (hn0 : n ≠ 0) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
  -- Split into cases whether `n` is large or small
  rcases lt_or_ge 511 n with h | h
  -- If `n` is large, apply the lemma derived from the inequalities on the central binomial
  -- coefficient.
  · exact exists_prime_lt_and_le_two_mul_eventually n h
  replace h : n < 521 := h.trans_lt (by norm_num1)
  revert h
  -- For small `n`, supply a list of primes to cover the initial cases.
  open Lean Elab Tactic in
  run_tac do
    for i in [317, 163, 83, 43, 23, 13, 7, 5, 3, 2] do
      let i : Term := quote i
      evalTactic <| ←
        `(tactic| refine exists_prime_lt_and_le_two_mul_succ $i (by norm_num1) (by norm_num1) ?_)
  exact fun h2 => ⟨2, prime_two, h2, Nat.mul_le_mul_left 2 (Nat.pos_of_ne_zero hn0)⟩

alias bertrand := Nat.exists_prime_lt_and_le_two_mul

end Nat

end Nat
