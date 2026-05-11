/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Data.Nat.Choose.Dvd

import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.SylvesterSchur.BlockReductions
import Mathlib.NumberTheory.SylvesterSchur.ResidualFinite
import Mathlib.NumberTheory.SylvesterSchur.ResidualLarge
import Mathlib.NumberTheory.SylvesterSchur.ResidualLargeCertificates

/-!
# Erdős key lemma

This is the core of Erdős's 1934 proof of Sylvester-Schur. The binomial coefficient
`Nat.choose (k + n - 1) n` must have a prime factor `p` with `n < p`
whenever `1 ≤ n` and `n < k`.
-/

@[expose] public section

namespace Nat.SylvesterSchur
namespace Internal

open Finset Nat

private lemma scaled_ternary_choose {N r : ℕ} (hr : 4 ≤ r) (hrN : 3 * r ≤ N)
    (hbound :
      r * (2 ^ r * ((3 * r) ^ r *
        4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N))) <
          3 ^ r * 4 ^ r * N ^ r) :
    ∃ p, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r :=
  exists_prime_dvd_choose_of_scaled_ternary_erdos_layers_bound hr hrN hbound

private lemma central_offset_div_three_choose {N r i : ℕ}
    (hr : 4 ≤ r) (hi : i ≤ r) (hN : N = 2 * r + i) (hN6 : 6 ≤ N)
    (hbound :
      r * (2 ^ i *
          (∏ j ∈ Finset.range (Nat.log 2 N),
            if j = 0 then primorial (N / 3)
            else primorial (Nat.nthRoot (j + 1) N))) <
        3 ^ i * 4 ^ r) :
    ∃ p, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r :=
  exists_prime_dvd_choose_of_central_offset_erdos_div_three_layers_bound
    hr hi hN hN6 hbound

private lemma exists_prime_dvd_choose_of_block_interval {n k p : ℕ}
    (hp : p.Prime) (hp_gt : n < p) (hp_ge : k ≤ p) (hp_le : p ≤ k + n - 1) :
    ∃ q, q.Prime ∧ n < q ∧ q ∣ Nat.choose (k + n - 1) n :=
  ⟨p, hp, hp_gt, prime_dvd_choose_of_mem_interval hp hp_gt hp_ge hp_le⟩

private lemma erdos_choose_prime_factor_gt_small_length
    (n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6) (k : ℕ) (hk : n + 3 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  interval_cases n
  · exact exists_prime_dvd_choose_of_large_prime_dvd_block
      (consecutive_two (k := k) (by omega))
  · exact exists_prime_dvd_choose_of_large_prime_dvd_block
      (consecutive_three (k := k) (by omega))
  · exact exists_prime_dvd_choose_of_large_prime_dvd_block
      (consecutive_four (k := k) (by omega))
  · exact exists_prime_dvd_choose_of_large_prime_dvd_block
      (consecutive_five (k := k) (by omega))
  · exact exists_prime_dvd_choose_of_large_prime_dvd_block
      (consecutive_six (k := k) (by omega))

private lemma erdos_choose_prime_factor_gt_length_one (k : ℕ) (hk : 1 < k) :
    ∃ p : ℕ, p.Prime ∧ 1 < p ∧ p ∣ Nat.choose (k + 1 - 1) 1 := by
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
  exact ⟨p, hp, by linarith [hp.two_le], by simp [Nat.choose_one_right, hp_dvd]⟩

private lemma erdos_choose_prime_factor_gt_base_start (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (n + 1 + n - 1) n := by
  obtain ⟨q, hq_prime, hq_gt, hq_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n (Nat.one_le_iff_ne_zero.mp hn)
  have hq_dvd : q ∣ Nat.choose (n + (n + 1 - 1)) n :=
    Nat.Prime.dvd_choose_add hq_prime hq_gt (by omega) (by omega)
  exact ⟨q, hq_prime, hq_gt, by
    rwa [show n + (n + 1 - 1) = n + 1 + n - 1 from by omega] at hq_dvd⟩

private lemma erdos_choose_prime_factor_gt_second_start (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (n + 2 + n - 1) n := by
  obtain ⟨p, hp, hp_gt, hp_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n + 1) (Nat.succ_ne_zero n)
  have hp_le_bd : p ≤ n + 2 + n - 1 := by
    rcases Nat.eq_or_lt_of_le hp_le with heq | hlt
    · exact absurd (heq ▸ hp) (Nat.not_prime_mul (by omega) (by omega))
    · omega
  exact exists_prime_dvd_choose_of_block_interval hp (by omega) (by omega) hp_le_bd

private lemma erdos_choose_prime_factor_gt_bound_dispatch_tail (n k : ℕ)
    (hn : 7 ≤ n) (hk : n + 3 ≤ k)
    (hblock_large : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i)
    (hprimeCounting_lower : k ^ n ≤ n ! * (k + n - 1) ^ Nat.primeCounting n)
    (hfallback :
      k ^ n ≤ n ! * (k + n - 1) ^ Nat.primeCounting n →
      (38 ≤ n → k ≤ n ^ 2) →
      ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  have hk_le_quadratic_start_bound : 38 ≤ n → k ≤ n ^ 2 := by
    intro hn38
    exact start_le_quadratic_of_no_large_prime_dvd_block hn38 hblock_large
  by_cases herdos_three :
      n ! *
          4 ^ (n + Nat.sqrt (k + n - 1) +
            Nat.nthRoot 3 (k + n - 1) * Nat.log 2 (k + n - 1)) <
        k ^ n
  · exact exists_prime_dvd_choose_of_erdos_layers_three_layers_bound
      (by omega) (by omega) herdos_three
  by_cases herdos_four :
      n ! * 4 ^ (n + Nat.sqrt (k + n - 1) * Nat.log 2 (k + n - 1)) < k ^ n
  · exact exists_prime_dvd_choose_of_erdos_layers_four_pow_bound
      (by omega) (by omega) herdos_four
  exact hfallback hprimeCounting_lower hk_le_quadratic_start_bound

private lemma erdos_choose_prime_factor_gt_bound_dispatch_core (n k : ℕ)
    (hn : 7 ≤ n) (hk : n + 3 ≤ k)
    (hfallback :
      k ^ n ≤ n ! * (k + n - 1) ^ Nat.primeCounting n →
      (38 ≤ n → k ≤ n ^ 2) →
      ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  by_cases hsmooth_count : 2 ^ Nat.primeCounting n * Nat.sqrt (k + n - 1) < n
  · exact exists_prime_dvd_choose_of_smooth_count_bound hsmooth_count
  by_cases hblock_large : ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i
  · exact exists_prime_dvd_choose_of_large_prime_dvd_block hblock_large
  by_cases hprimeCounting : n ! * (k + n - 1) ^ Nat.primeCounting n < k ^ n
  · exact exists_prime_dvd_choose_of_primeCounting_bound (by omega) (by omega) hprimeCounting
  by_cases hsqrt :
      n ! * ((k + n - 1) ^ (Nat.sqrt (k + n - 1) + 1) * primorial n) < k ^ n
  · exact exists_prime_dvd_choose_of_sqrt_primorial_bound (by omega) (by omega) hsqrt
  by_cases hdiv_three_erdos :
      n ! *
          (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
            if j = 0 then primorial ((k + n - 1) / 3)
            else primorial (Nat.nthRoot (j + 1) (k + n - 1))) <
        k ^ n
  · exact exists_prime_dvd_choose_of_erdos_div_three_layers_bound
      (by omega) (by omega) (by omega) hdiv_three_erdos
  by_cases herdos :
      n ! *
          (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
            if j = 0 then primorial n
            else primorial (Nat.nthRoot (j + 1) (k + n - 1))) <
        k ^ n
  · exact exists_prime_dvd_choose_of_erdos_layers_bound (by omega) (by omega) herdos
  by_cases hhalf : n ! * (k + n - 1) ^ (n / 2 + 1) < k ^ n
  · exact exists_prime_dvd_choose_of_half_bound (by omega) (by omega) hhalf
  by_cases hlarge : n ! * 2 ^ (n - 1) < k
  · exact exists_prime_dvd_choose_of_large_start (by omega) (by omega) hlarge
  exact erdos_choose_prime_factor_gt_bound_dispatch_tail n k hn hk hblock_large
    (le_of_not_gt hprimeCounting) hfallback

private lemma erdos_choose_prime_factor_gt_second_residual_large (n k : ℕ)
    (hn945 : 945 ≤ n) (hk : n + 3 ≤ k)
    (hscaled_ternary :
      ¬ (3 * n ≤ k + n - 1 ∧
        n * (2 ^ n * ((3 * n) ^ n *
          4 ^ (n + Nat.sqrt (k + n - 1) +
            Nat.nthRoot 3 (k + n - 1) * Nat.log 2 (k + n - 1)))) <
        3 ^ n * 4 ^ n * (k + n - 1) ^ n))
    (hcentral_offset :
      ¬ (k + n - 1 < 3 * n ∧
        n * (2 ^ (k - n - 1) *
          (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
            if j = 0 then primorial ((k + n - 1) / 3)
            else primorial (Nat.nthRoot (j + 1) (k + n - 1)))) <
        3 ^ (k - n - 1) * 4 ^ n))
    (hk_le_quadratic_start_bound : 38 ≤ n → k ≤ n ^ 2) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  by_cases hN3 : 3 * n ≤ k + n - 1
  · have hNhi : k + n - 1 ≤ n ^ 2 + n := by
      have hkquad := hk_le_quadratic_start_bound (by omega : 38 ≤ n)
      omega
    exact False.elim <| hscaled_ternary ⟨hN3,
      first_residual_large_scaled_ternary_bound hn945 hN3 hNhi⟩
  exact False.elim <| hcentral_offset ⟨by omega,
    second_residual_large_central_offset_bound hn945 (by omega) (by omega)⟩

private lemma erdos_choose_prime_factor_gt_second_residual_finite (n k : ℕ)
    (hn : 7 ≤ n) (hk : n + 3 ≤ k) (hnlt945 : n < 945)
    (hprimeCounting_lower : k ^ n ≤ n ! * (k + n - 1) ^ Nat.primeCounting n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  by_cases hn38 : 38 ≤ n
  · by_cases hk1291 : 1291 ≤ k
    · exact False.elim <| (not_lt_of_ge hprimeCounting_lower) <|
        second_residual_mid_primeCounting_lt_start_pow hn38 hnlt945 hk1291
    have hklt1291 : k < 1291 := by omega
    exact exists_prime_dvd_choose_of_large_prime_dvd_block
      (second_residual_mid_has_large_prime_factor hn38 hnlt945 (by omega) hklt1291)
  have hnlt38 : n < 38 := by omega
  by_cases hk100 : 100 ≤ k
  · exact False.elim <| (not_lt_of_ge hprimeCounting_lower) <|
      second_residual_tiny_primeCounting_lt_start_pow hn hnlt38 hk100
  have hklt100 : k < 100 := by omega
  exact exists_prime_dvd_choose_of_large_prime_dvd_block
    (second_residual_tiny_has_large_prime_factor hn hnlt38 (by omega) hklt100)

private lemma erdos_choose_prime_factor_gt_second_residual (n k : ℕ)
    (hn : 7 ≤ n) (hk : n + 3 ≤ k)
    (hprimeCounting_lower : k ^ n ≤ n ! * (k + n - 1) ^ Nat.primeCounting n)
    (hk_le_quadratic_start_bound : 38 ≤ n → k ≤ n ^ 2) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  by_cases hscaled_ternary :
      3 * n ≤ k + n - 1 ∧
        n * (2 ^ n * ((3 * n) ^ n *
          4 ^ (n + Nat.sqrt (k + n - 1) +
            Nat.nthRoot 3 (k + n - 1) * Nat.log 2 (k + n - 1)))) <
        3 ^ n * 4 ^ n * (k + n - 1) ^ n
  · obtain ⟨hN3, hscaled_bound⟩ := hscaled_ternary
    exact scaled_ternary_choose (N := k + n - 1) (r := n) (by omega) hN3 hscaled_bound
  by_cases hcentral_offset :
      k + n - 1 < 3 * n ∧
        n * (2 ^ (k - n - 1) *
          (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
            if j = 0 then primorial ((k + n - 1) / 3)
            else primorial (Nat.nthRoot (j + 1) (k + n - 1)))) <
        3 ^ (k - n - 1) * 4 ^ n
  · obtain ⟨hcentral_range, hcentral_bound⟩ := hcentral_offset
    exact central_offset_div_three_choose (N := k + n - 1) (r := n) (i := k - n - 1)
      (by omega) (by omega) (by omega) (by omega) hcentral_bound
  by_cases hn945 : 945 ≤ n
  · exact erdos_choose_prime_factor_gt_second_residual_large n k hn945 hk
      hscaled_ternary hcentral_offset hk_le_quadratic_start_bound
  have hnlt945 : n < 945 := by omega
  exact erdos_choose_prime_factor_gt_second_residual_finite n k hn hk hnlt945
    hprimeCounting_lower

private lemma erdos_choose_prime_factor_gt_of_bertrand_overshoot (n k t : ℕ)
    (hn : 7 ≤ n) (hk : n + 3 ≤ k) (ht : t.Prime)
    (ht_ge : t ≥ k) (ht_not_range : ¬ t ≤ k + n - 1)
    (ht_le : t ≤ 2 * (n + 2)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  have hk_n3 : k = n + 3 := by
    by_contra hk_ne
    have ht_val : t = 2 * n + 4 := by omega
    have h2n4_not_prime : ¬ (2 * n + 4).Prime := by
      rw [show 2 * n + 4 = 2 * (n + 2) from by ring]
      exact Nat.not_prime_mul (by omega) (by omega)
    exact h2n4_not_prime (ht_val ▸ ht)
  subst hk_n3
  by_cases hn512 : 512 ≤ n
  · simpa [gt_iff_lt, show n + 3 + n - 1 = 2 * n + 2 by omega] using
      exists_large_prime_dvd_choose_of_mul_prod_erdos_central_layers_lt_four_pow
        (N := 2 * n + 2) (r := n) (by omega) (by omega) (by omega) (by omega)
        (central_erdos_layers_two_mul_add_two_lt_four_pow hn512)
  simpa [gt_iff_lt, show n + 3 + n - 1 = 2 * n + 2 by omega] using
    exists_prime_dvd_choose_two_mul_add_two_small hn (by omega : n < 512)

private lemma erdos_choose_prime_factor_gt_bertrand_steps (n k : ℕ)
    (hn : 7 ≤ n) (hk : n + 3 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  obtain ⟨r, hr, hr_gt, hr_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n + 1) (Nat.succ_ne_zero n)
  by_cases hr_gek : r ≥ k
  · exact exists_prime_dvd_choose_of_block_interval hr (by omega) hr_gek (by omega)
  by_cases hr_easy : r = n + 2 ∧ ¬ r ∣ k - 1 ∧ ¬ r ∣ k - 2
  · obtain ⟨hr_n2, hr_not_one, hr_not_two⟩ := hr_easy
    obtain ⟨i, hi, hr_dvd⟩ := exists_dvd_block_of_succ_succ_prime_not_dvd_pred
      (n := n) (k := k) (s := r) (by omega) hr_n2 hr_not_one hr_not_two
    exact ⟨r, hr, by omega, prime_dvd_seq_implies_choose hr (by omega) i hi hr_dvd⟩
  obtain ⟨t, ht, ht_gt, ht_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n + 2) (Nat.succ_ne_zero (n + 1))
  by_cases ht_gek : t ≥ k
  · by_cases ht_range : t ≤ k + n - 1
    · exact exists_prime_dvd_choose_of_block_interval ht (by omega) ht_gek ht_range
    exact erdos_choose_prime_factor_gt_of_bertrand_overshoot
      n k t hn hk ht ht_gek ht_range ht_le
  obtain ⟨B, hB, hB_gt, hB_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (k - 1) (by omega)
  by_cases hB_range : B ≤ k + n - 1
  · exact exists_prime_dvd_choose_of_block_interval hB (by omega) (by omega) hB_range
  exact erdos_choose_prime_factor_gt_bound_dispatch_core n k hn hk
    (erdos_choose_prime_factor_gt_second_residual n k hn hk)

/- Hard case of the Erdős key lemma: for `2 ≤ n` and `n + 3 ≤ k`,
`Nat.choose (k + n - 1) n` has a prime factor greater than `n`.

This packages the small-length cases, Bertrand steps, and residual estimates needed after
the direct absorption cases have been eliminated. -/
private lemma erdos_choose_prime_factor_gt_hard
    (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : n + 3 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  by_cases hn6 : n ≤ 6
  · exact erdos_choose_prime_factor_gt_small_length n hn hn6 k hk
  have hn7 : 7 ≤ n := by omega
  exact erdos_choose_prime_factor_gt_bertrand_steps n k hn7 hk

/-- **Erdős key lemma** (1934): for `1 ≤ n < k`, the binomial coefficient
`Nat.choose (k + n - 1) n` has a prime factor strictly greater than `n`.

The cases `n = 1`, `k = n + 1`, and `k = n + 2` are direct Bertrand arguments.
All later starts are handled by the consolidated hard-case estimate above. -/
lemma erdos_choose_prime_factor_gt (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : n < k) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  by_cases hn1 : n = 1
  · subst hn1
    exact erdos_choose_prime_factor_gt_length_one k hk
  have hn2 : 2 ≤ n := by omega
  by_cases hkn1 : k = n + 1
  · subst hkn1
    exact erdos_choose_prime_factor_gt_base_start n hn
  by_cases hkn2 : k = n + 2
  · subst hkn2
    exact erdos_choose_prime_factor_gt_second_start n hn2
  exact erdos_choose_prime_factor_gt_hard n hn2 k (by omega)

end Internal
end Nat.SylvesterSchur
