/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.NumberTheory.SylvesterSchur.ErdosPowerBounds

/-!
# Large-prime criteria for Sylvester-Schur

This file collects contrapositive criteria that turn explicit binomial
coefficient inequalities into large prime divisors.
-/

@[expose] public section

namespace Nat.SylvesterSchur

open scoped BigOperators

open Finset Nat

/- Contrapositive of the sharpened Erdős layer bound. -/
private lemma exists_large_prime_dvd_choose_of_prod_erdos_layers_lt_choose {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N)
    (hbound :
      (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) <
        Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge (choose_le_prod_erdos_layers_of_no_large hN hrN hsmall)) hbound

/- Rational lower-bound formulation using the sharpened Erdős layer bound. -/
private lemma exists_large_prime_dvd_choose_of_prod_erdos_layers_lt_lower_bound {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N)
    (hbound :
      (((∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N) : ℕ) : ℚ) <
        ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ))) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall => choose_le_prod_erdos_layers_of_no_large hN hrN hsmall) hbound

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_prod_erdos_layers_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_layers_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hbound :
      r ! * (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) <
        (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_prod_erdos_layers_lt_lower_bound hN hrN
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

/- Contrapositive of the full Erdős prime-power layer bound. -/
private lemma exists_large_prime_dvd_choose_of_prod_primorial_nthRoot_lt_choose {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N)
    (hbound :
      (∏ j ∈ Finset.range (Nat.log 2 N), primorial (Nat.nthRoot (j + 1) N)) <
        Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge (choose_le_prod_primorial_nthRoot_of_no_large hN hrN hsmall))
    hbound

/- Rational lower-bound formulation using the full Erdős prime-power layer bound. -/
private lemma exists_large_prime_dvd_choose_of_prod_primorial_nthRoot_lt_lower_bound {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N)
    (hbound :
      (((∏ j ∈ Finset.range (Nat.log 2 N), primorial (Nat.nthRoot (j + 1) N) : ℕ) : ℚ) <
        ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ))) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall => choose_le_prod_primorial_nthRoot_of_no_large hN hrN hsmall) hbound

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_prod_primorial_nthRoot_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_prod_primorial_nthRoot_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hbound :
      r ! * (∏ j ∈ Finset.range (Nat.log 2 N), primorial (Nat.nthRoot (j + 1) N)) <
        (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_prod_primorial_nthRoot_lt_lower_bound hN hrN
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

private lemma choose_small_factorization_product_le_top_pow_sqrt {N r : ℕ} (hN : 0 < N) :
    (∏ p ∈ (Finset.range (r + 1)).filter (fun p => p ≤ Nat.sqrt N),
        p ^ (Nat.choose N r).factorization p) ≤ N ^ (Nat.sqrt N + 1) := by
  classical
  calc
    (∏ p ∈ (Finset.range (r + 1)).filter (fun p => p ≤ Nat.sqrt N),
        p ^ (Nat.choose N r).factorization p) ≤
        ∏ _p ∈ (Finset.range (r + 1)).filter (fun p => p ≤ Nat.sqrt N), N := by
          apply Finset.prod_le_prod'
          intro p hp
          by_cases hp_prime : p.Prime
          · exact Nat.pow_factorization_choose_le hN
          · rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime, pow_zero]
            exact hN
    _ = N ^ ((Finset.range (r + 1)).filter (fun p => p ≤ Nat.sqrt N)).card := by
      rw [Finset.prod_const]
    _ ≤ N ^ (Nat.sqrt N + 1) := by
      apply Nat.pow_le_pow_right hN
      have hcard :
          ((Finset.range (r + 1)).filter (fun p => p ≤ Nat.sqrt N)).card ≤
            (Finset.range (Nat.sqrt N + 1)).card :=
        Finset.card_le_card fun p hp => by
          rw [Finset.mem_filter, Finset.mem_range] at hp
          exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hp.2)
      simpa using hcard

private lemma choose_factorization_pow_le_self_of_sqrt_lt {N r p : ℕ}
    (hp_prime : p.Prime) (hp_large : Nat.sqrt N < p) :
    p ^ (Nat.choose N r).factorization p ≤ p := by
  have hpow_le_one : (Nat.choose N r).factorization p ≤ 1 :=
    Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp hp_large)
  exact (Nat.pow_le_pow_right hp_prime.one_le hpow_le_one).trans_eq (pow_one p)

private lemma choose_large_factorization_product_le_primorial (N r : ℕ) :
    (∏ p ∈ (Finset.range (r + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N),
        p ^ (Nat.choose N r).factorization p) ≤ primorial r := by
  classical
  let large : Finset ℕ := (Finset.range (r + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N)
  let f : ℕ → ℕ := fun p => p ^ (Nat.choose N r).factorization p
  have hfilter : ∏ p ∈ large, f p = ∏ p ∈ large.filter Nat.Prime, f p := by
    exact (Finset.prod_filter_of_ne (s := large) (p := Nat.Prime) (f := f) (by
      intro p _ hp_ne_one
      contrapose! hp_ne_one
      dsimp [f]
      rw [Nat.factorization_eq_zero_of_not_prime _ hp_ne_one, pow_zero])).symm
  rw [show (∏ p ∈ (Finset.range (r + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N),
      p ^ (Nat.choose N r).factorization p) = ∏ p ∈ large, f p by rfl, hfilter]
  refine (Finset.prod_le_prod'
    (s := large.filter Nat.Prime) (f := f) (g := fun p => p) fun p hp => ?_).trans ?_
  · obtain ⟨hlarge, hp_prime⟩ := Finset.mem_filter.mp hp
    exact choose_factorization_pow_le_self_of_sqrt_lt hp_prime (by
      dsimp [large] at hlarge
      rw [Finset.mem_filter] at hlarge
      omega)
  dsimp [primorial]
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    dsimp [large] at hp
    rw [Finset.mem_filter] at hp
    exact ⟨hp.1.1, hp.2⟩
  · intro p hp _hp_not
    exact (Finset.mem_filter.mp hp).2.one_le

/- Erdős-style split of the no-large-prime factorization at `sqrt N`.

Prime factors at most `sqrt N` each contribute at most `N`; prime factors above `sqrt N`
occur with multiplicity at most one, so their contribution is bounded by the primorial of `r`.
This is weaker than the full 1934 product estimate, but it is the next useful refinement beyond
the crude `N ^ Nat.primeCounting r` bound. -/
private lemma choose_le_top_pow_sqrt_mul_primorial_of_no_large {N r : ℕ} (hN : 0 < N)
    (hrN : r ≤ N) (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    Nat.choose N r ≤ N ^ (Nat.sqrt N + 1) * primorial r := by
  classical
  rw [← choose_eq_prod_small_prime_powers_of_no_large hrN hsmall]
  let f : ℕ → ℕ := fun p => p ^ (Nat.choose N r).factorization p
  let small : Finset ℕ := (Finset.range (r + 1)).filter (fun p => p ≤ Nat.sqrt N)
  let large : Finset ℕ := (Finset.range (r + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N)
  have hsplit :
      (∏ p ∈ Finset.range (r + 1), f p) =
        (∏ p ∈ small, f p) * (∏ p ∈ large, f p) := by
    dsimp [small, large]
    exact (Finset.prod_filter_mul_prod_filter_not
      (Finset.range (r + 1)) (fun p => p ≤ Nat.sqrt N) f).symm
  rw [hsplit]
  apply Nat.mul_le_mul
  · simpa [small, f] using choose_small_factorization_product_le_top_pow_sqrt (N := N) (r := r) hN
  · simpa [large, f] using choose_large_factorization_product_le_primorial N r

/- Contrapositive of `choose_le_top_pow_sqrt_mul_primorial_of_no_large`. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_sqrt_mul_primorial_lt_choose {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N)
    (hbound : N ^ (Nat.sqrt N + 1) * primorial r < Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge
    (choose_le_top_pow_sqrt_mul_primorial_of_no_large hN hrN hsmall)) hbound

/-- Near the central range, the central-binomial lower bound turns the split factorization bound
into a large-prime criterion. -/
theorem exists_large_prime_dvd_choose_of_mul_top_pow_sqrt_mul_primorial_lt_four_pow
    {N r : ℕ} (hr : 4 ≤ r) (hN : 2 * r ≤ N)
    (hbound : r * (N ^ (Nat.sqrt N + 1) * primorial r) < 4 ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_top_pow_sqrt_mul_primorial_lt_choose
  · omega
  · omega
  have hcentral_le : Nat.centralBinom r ≤ Nat.choose N r := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.choose_le_choose r hN
  have hlower : 4 ^ r < r * Nat.choose N r := by
    exact (Nat.four_pow_lt_mul_centralBinom r hr).trans_le
      (Nat.mul_le_mul_left r hcentral_le)
  by_contra hnot
  push Not at hnot
  have hmul : r * Nat.choose N r ≤ r * (N ^ (Nat.sqrt N + 1) * primorial r) :=
    Nat.mul_le_mul_left r hnot
  exact (not_lt_of_ge hbound.le) (hlower.trans_le hmul)

/- Rational lower-bound formulation using the split `sqrt/primorial` upper bound. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_sqrt_mul_primorial_lt_lower_bound
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hbound :
      (((N ^ (Nat.sqrt N + 1) * primorial r : ℕ) : ℚ) <
        ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ))) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall => choose_le_top_pow_sqrt_mul_primorial_of_no_large hN hrN hsmall) hbound

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_top_pow_sqrt_mul_primorial_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hbound : r ! * (N ^ (Nat.sqrt N + 1) * primorial r) < (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_top_pow_sqrt_mul_primorial_lt_lower_bound hN hrN
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

/- Contrapositive form of the factorization estimate: if `Nat.choose N r` is larger than the
no-large-prime upper bound, then it has a prime divisor exceeding `r`. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_primeCounting_lt_choose {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N)
    (hbound : N ^ Nat.primeCounting r < Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge (choose_le_top_pow_primeCounting_of_no_large hN hrN hsmall)) hbound

/- A variant using only the elementary estimate `Nat.primeCounting r ≤ r - 1`. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_sub_one_lt_choose {N r : ℕ}
    (hN : 0 < N) (hr : 2 ≤ r) (hrN : r ≤ N)
    (hbound : N ^ (r - 1) < Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge (choose_le_top_pow_sub_one_of_no_large hN hr hrN hsmall)) hbound

/- A variant using the formalized `π(r) ≤ r / 2 + 1` estimate. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_half_add_one_lt_choose {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N) (hbound : N ^ (r / 2 + 1) < Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge (choose_le_top_pow_half_add_one_of_no_large hN hrN hsmall)) hbound

/- A variant using the explicit Erdős-style estimate `Nat.primeCounting r ≤ 3 * r / 8`. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_three_mul_div_eight_lt_choose
    {N r : ℕ} (hN : 0 < N) (hr : 38 ≤ r) (hrN : r ≤ N)
    (hbound : N ^ (3 * r / 8) < Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge
    (choose_le_top_pow_three_mul_div_eight_of_no_large hN hr hrN hsmall)) hbound

/- A rational lower-bound formulation convenient for later analytic estimates.  Once a separate
calculation proves that this lower bound already exceeds the no-large-prime upper bound, a large
prime divisor follows. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_primeCounting_lt_lower_bound {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N)
    (hbound :
      ((N ^ Nat.primeCounting r : ℕ) : ℚ) < ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ)) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall => choose_le_top_pow_primeCounting_of_no_large hN hrN hsmall) hbound

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_top_pow_primeCounting_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_top_pow_primeCounting_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hbound : r ! * N ^ Nat.primeCounting r < (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_top_pow_primeCounting_lt_lower_bound hN hrN
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

/- Lower-bound criterion using the formalized `π(r) ≤ r / 2 + 1` estimate. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_half_add_one_lt_lower_bound {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N)
    (hbound : ((N ^ (r / 2 + 1) : ℕ) : ℚ) < ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ)) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall => choose_le_top_pow_half_add_one_of_no_large hN hrN hsmall) hbound

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_top_pow_half_add_one_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_top_pow_half_add_one_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N)
    (hbound : r ! * N ^ (r / 2 + 1) < (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_top_pow_half_add_one_lt_lower_bound hN hrN
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

/- Lower-bound criterion using the explicit `π(r) ≤ 3r/8` estimate. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_three_mul_div_eight_lt_lower_bound
    {N r : ℕ} (hN : 0 < N) (hr : 38 ≤ r) (hrN : r ≤ N)
    (hbound :
      ((N ^ (3 * r / 8) : ℕ) : ℚ) < ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ)) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall => choose_le_top_pow_three_mul_div_eight_of_no_large hN hr hrN hsmall)
    hbound

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_top_pow_three_mul_div_eight_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_top_pow_three_mul_div_eight_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hr : 38 ≤ r) (hrN : r ≤ N)
    (hbound : r ! * N ^ (3 * r / 8) < (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_top_pow_three_mul_div_eight_lt_lower_bound hN hr hrN
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

/-- A power-only variant of the `3r/8` criterion, using `r! ≤ r ^ r`. -/
theorem exists_large_prime_dvd_choose_of_self_pow_mul_top_pow_three_mul_div_eight_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hr : 38 ≤ r) (hrN : r ≤ N)
    (hbound : r ^ r * N ^ (3 * r / 8) < (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_factorial_mul_top_pow_three_mul_div_eight_lt_lower_pow
    hN hr hrN
  exact (Nat.mul_le_mul_right (N ^ (3 * r / 8)) (Nat.factorial_le_pow r)).trans_lt
    hbound

/- The same lower-bound criterion with the elementary exponent `r - 1`. -/
private lemma exists_large_prime_dvd_choose_of_top_pow_sub_one_lt_lower_bound {N r : ℕ}
    (hN : 0 < N) (hr : 2 ≤ r) (hrN : r ≤ N)
    (hbound : ((N ^ (r - 1) : ℕ) : ℚ) < ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ)) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall => choose_le_top_pow_sub_one_of_no_large hN hr hrN hsmall) hbound

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_top_pow_sub_one_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sub_one_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hr : 2 ≤ r) (hrN : r ≤ N)
    (hbound : r ! * N ^ (r - 1) < (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_top_pow_sub_one_lt_lower_bound hN hr hrN
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

end Nat.SylvesterSchur
