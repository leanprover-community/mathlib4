/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.SmoothNumbers

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum.NatSqrt

/-!
# Chebyshev's Lower Bound on Primorial

We prove `2 ^ (n / 2 + 1) ≤ n#` for `n ≥ 5` and `2 ^ ((n + 1) / 2) ≤ n#` for `n ≥ 2`, where
`n#` denotes the primorial (product of all primes ≤ n). These are the lower bound complements to
`primorial_le_four_pow` (which gives the upper bound `n# ≤ 4^n`).

## Proof technique

Central binomial decomposition: from `4^n < n * C(2n,n)` (`four_pow_lt_mul_centralBinom`) and
`v_p(C(2n,n)) ≤ log_p(2n)` (`factorization_choose_le_log`), we bound `C(2n,n)` above by
`(2n)^{π(√(2n))} * (2n)#`. Rearranging gives `(2n)# ≥ 2^n` for `n ≥ 29`.

The key analytical step shows `(log₂(2n)+1) * (√(2n)+2) ≤ n` for `n > 400` by factoring
through `r = √n`:
- `2*(log₂(2n)+1) ≤ r` via `2n < 2^(r/2)` (exponential beats polynomial)
- `√(2n)+2 ≤ 2*r` via `zify` + `nlinarith`
- Combine with `r² ≤ n`

Base cases `n ∈ [3, 29]` by computation.

## Main results

- `two_pow_succ_lt_primorial`: `2 ^ (n + 1) < (2 * n)#` for `n ≥ 3`
- `two_pow_lt_primorial`: `2 ^ n < (2 * n)#` for `n ≥ 2`
- `two_pow_le_primorial`: `2 ^ n ≤ (2 * n)#` for all `n`
- `two_pow_half_add_one_le_primorial`: `2 ^ (n / 2 + 1) ≤ n#` for `n ≥ 5`
- `two_pow_half_succ_le_primorial`: `2 ^ ((n + 1) / 2) ≤ n#` for `n ≥ 2`
- `two_pow_div_two_le_primorial`: `2 ^ (n / 2) ≤ n#` for all `n`
-/

@[expose] public section

open Finset Nat

local notation x "#" => primorial x

/-- `C(2n, n) ≤ (2n)^{π(√(2n))} * (2n)#` for `n ≥ 4`. -/
theorem centralBinom_le_pow_mul_primorial {n : ℕ} (hn : 4 ≤ n) :
    centralBinom n ≤ (2 * n) ^ (sqrt (2 * n) + 1).primesBelow.card * (2 * n)# := by
  set s := sqrt (2 * n)
  let f x := x ^ (centralBinom n).factorization x
  have hS : ∏ x ∈ (2 * n + 1).primesBelow, f x = ∏ x ∈ range (2 * n + 1), f x := by
    refine prod_filter_of_ne fun p _ h ↦ ?_
    contrapose! h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime _ h, pow_zero]
  rw [← prod_pow_factorization_centralBinom, ← hS,
    ← prod_filter_mul_prod_filter_not _ (· ≤ s)]
  gcongr
  · have hfilt : (2 * n + 1).primesBelow.filter (· ≤ s) = (s + 1).primesBelow := by
      have : s ≤ 2 * n := sqrt_le_self _
      ext p; simp only [Finset.mem_filter, mem_primesBelow]
      exact ⟨fun ⟨⟨_, hp⟩, hle⟩ ↦ ⟨by lia, hp⟩, fun ⟨hlt, hp⟩ ↦ ⟨⟨by lia, hp⟩, by lia⟩⟩
    rw [hfilt]
    exact prod_le_pow_card _ _ _ fun _ _ ↦ pow_factorization_choose_le (by lia)
  · rw [primorial, ← primesBelow]
    have H : ∀ p ∈ {x ∈ (2 * n + 1).primesBelow | ¬x ≤ s}, f p ≤ p := by
      intro p hp
      nth_rewrite 2 [← pow_one p]
      exact pow_le_pow_right₀ (by grind) <| factorization_choose_le_one <| sqrt_lt'.mp (by grind)
    refine prod_le_prod' H |>.trans ?_
    exact prod_le_prod_of_subset_of_one_le (filter_subset ..) (by lia)
      fun p hp _ ↦ (prime_of_mem_primesBelow hp).one_le

/-- `8u² + 16u + 8 ≤ 2^u` for `u ≥ 10`. -/
theorem eight_mul_sq_add_le_two_pow (u : ℕ) (hu : 10 ≤ u) :
    8 * u ^ 2 + 16 * u + 8 ≤ 2 ^ u := by
  rw [show 8 * u ^ 2 + 16 * u + 8 = 8 * (u + 1) ^ 2 by lia]
  induction u, hu using Nat.le_induction with
  | base => decide
  | succ u hu ih =>
    rw [show (u + 1 + 1) ^ 2 = (u + 1) ^ 2 + (u + 3 + u) by lia, mul_add, pow_succ' 2, two_mul]
    exact Nat.add_le_add ih (ih.trans' (by nlinarith))

/-- `(2n)^{π(√(2n))+1} ≤ 2^n` for `n ≥ 30`. -/
private theorem numerical_bound_aux (n l u k : ℕ) (hl : l ≤ n := by lia) (hu : n ≤ u := by lia)
    (hu₀ : 0 < u := by lia) (H : (2 * u) ^ (k + 1) ≤ 2 ^ l := by norm_num)
    (hπ : #((2 * u).sqrt + 1).primesBelow = k := by norm_num [primesBelow]; decide) :
    (2 * n) ^ (#((2 * n).sqrt + 1).primesBelow + 1) ≤ 2 ^ n := by
  set π := #((2 * n).sqrt + 1).primesBelow
  have hcard : π ≤ k := by
    rw [← hπ]
    exact card_le_card <| filter_subset_filter _ <| range_subset_range.mpr (by gcongr)
  calc (2 * n) ^ (π + 1)
      ≤ (2 * u) ^ (π + 1) := Nat.pow_le_pow_left (by gcongr) _
    _ ≤ (2 * u) ^ (k + 1) := pow_le_pow_right₀ (by lia) (by lia)
    _ ≤ 2 ^ l := H
    _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hl

private theorem numerical_bound_aux' {n : ℕ} (hn : 400 ≤ n) :
    (2 * n) ^ (#((2 * n).sqrt + 1).primesBelow + 1) ≤ 2 ^ n := by
  set π := (sqrt (2 * n) + 1).primesBelow.card
  have hπ : π ≤ sqrt (2 * n) + 1 :=
    (card_filter_le _ _).trans (card_range _).le
  set s := sqrt (2 * n)
  set L := Nat.log 2 (2 * n)
  have h2n_bound : 2 * n < 2 ^ (L + 1) := lt_pow_succ_log_self (by lia) (2 * n)
  suffices h : (L + 1) * (s + 2) ≤ n by
    calc (2 * n) ^ (π + 1)
        ≤ (2 * n) ^ (s + 2) := by gcongr; lia
      _ ≤ (2 ^ (L + 1)) ^ (s + 2) := (Nat.pow_lt_pow_left h2n_bound (by lia)).le
      _ = 2 ^ ((L + 1) * (s + 2)) := (pow_mul ..).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by lia) h
  set r := sqrt n
  have hr_ge : 20 ≤ r := le_sqrt.mpr (by lia)
  have hr_sq : r * r ≤ n := sqrt_le n
  have hr_lt : n < (r + 1) * (r + 1) := lt_succ_sqrt n
  have hb : s + 2 ≤ 2 * r := by
    suffices hslt : s < 2 * r - 1 by lia
    rw [show s = sqrt (2 * n) from rfl, sqrt_lt]
    zify [show 1 ≤ 2 * r from by lia]
    nlinarith [sq_nonneg (r : ℤ)]
  have ha : 2 * (L + 1) ≤ r := by
    suffices L < r / 2 by lia
    suffices 2 * n < 2 ^ (r / 2) from (Nat.log_lt_iff_lt_pow one_lt_two (by lia)).mpr this
    calc 2 * n
        < 2 * ((r + 1) * (r + 1)) := by gcongr
      _ ≤ 2 * ((2 * (r / 2) + 2) * (2 * (r / 2) + 2)) := by gcongr <;> lia
      _ = 8 * (r / 2) ^ 2 + 16 * (r / 2) + 8 := by ring
      _ ≤ 2 ^ (r / 2) := eight_mul_sq_add_le_two_pow (r / 2) (by lia)
  nlinarith

/-- `(2n)^{π(√(2n))+1} ≤ 2^n` for `n ≥ 30`. -/
private theorem numerical_bound {n : ℕ} (hn : 30 ≤ n) :
    (2 * n) ^ ((sqrt (2 * n) + 1).primesBelow.card + 1) ≤ 2 ^ n := by
  set π := (sqrt (2 * n) + 1).primesBelow.card
  have hπ : π ≤ sqrt (2 * n) + 1 :=
    (card_filter_le _ _).trans (card_range _).le
  rcases le_or_gt 400 n with h_large | h_small
  · -- n > 400: factor through r = √n
    exact numerical_bound_aux' h_large
  · -- 30 ≤ n ≤ 400: bound π by range, then compute
    rcases le_or_gt n 32 with h₁ | h₁
    · -- n ∈ [30, 32]: π ≤ 4, (2*32)^5 = 64^5 = 2^30
      exact numerical_bound_aux n 30 32 4
    rcases le_or_gt n 44 with h₂ | h₂
    · -- n ∈ [33, 44]: π ≤ 4
      exact numerical_bound_aux n 33 44 4
    rcases le_or_gt n 84 with h₃ | h₃
    · -- n ∈ [45, 84]: π ≤ 5
      exact numerical_bound_aux n 45 84 5
    rcases le_or_gt n 264 with h₄ | h₄
    · -- n ∈ [85, 264]: π ≤ 8
      exact numerical_bound_aux n 85 264 8
    · -- n ∈ [265, 400]: π ≤ 9
      set_option exponentiation.threshold 300 in
      refine numerical_bound_aux n 265 400 9

/-- `2 ^ (n + 1) < (2n)#` for `n ≥ 3`. The core Chebyshev lower bound from which all
weaker variants are derived. -/
theorem two_pow_succ_lt_primorial {n : ℕ} (hn : 3 ≤ n) : 2 ^ (n + 1) < (2 * n)# := by
  obtain hn' | hn' := le_or_gt 30 n
  · have h4 : 4 ≤ n := by lia
    set π := (sqrt (2 * n) + 1).primesBelow.card
    apply lt_of_mul_lt_mul_left' (a := n * (2 * n) ^ π)
    calc
      _ ≤ 4 ^ n := by
        rw [show n * (2 * n) ^ π * 2 ^ (n + 1) = (2 * n) ^ (π + 1) * 2 ^ n from by ring,
          show (4 : ℕ) ^ n = 2 ^ n * 2 ^ n from by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul, two_mul, ← pow_add]]
        exact Nat.mul_le_mul_right _ (numerical_bound hn')
      _ < n * n.centralBinom := four_pow_lt_mul_centralBinom _ h4
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_left _ (centralBinom_le_pow_mul_primorial h4)
  · decide +revert

/-- **Strict Chebyshev lower bound**. `2 ^ n < (2n)#` for all `n ≥ 2`. -/
theorem two_pow_lt_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ^ n < (2 * n)# := by
  rcases Nat.lt_or_eq_of_le hn with hn | rfl
  · exact (Nat.pow_lt_pow_right (by lia) (by lia)).trans (two_pow_succ_lt_primorial (by lia))
  · decide

/-- **Even Chebyshev lower bound**. `2 ^ n ≤ (2n)#` for all `n`. -/
theorem two_pow_le_primorial {n : ℕ} : 2 ^ n ≤ (2 * n)# := by
  obtain hn | hn := le_or_gt 2 n
  · exact (two_pow_lt_primorial hn).le
  · decide +revert

/-- **Strongest Chebyshev lower bound**. `2 ^ (n / 2 + 1) ≤ n#` for `n ≥ 5`. -/
theorem two_pow_half_add_one_le_primorial {n : ℕ} (hn : 5 ≤ n) : 2 ^ (n / 2 + 1) ≤ n# := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · grind [two_pow_succ_lt_primorial]
  · rw [← primorial_succ (by lia) ⟨k, rfl⟩]
    grind [two_pow_lt_primorial (show 2 ≤ k + 1 by lia)]

/-- **Stronger Chebyshev lower bound**. `2 ^ ((n + 1) / 2) ≤ n#` for `n ≥ 2`. -/
theorem two_pow_half_succ_le_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ^ ((n + 1) / 2) ≤ n# := by
  obtain hn | hn := le_or_gt 5 n
  · exact (pow_le_pow_right₀ (by lia) (by lia)).trans (two_pow_half_add_one_le_primorial hn)
  · decide +revert

/-- **Chebyshev lower bound** (1852). `2 ^ (n / 2) ≤ n#` for all `n`.

The product of all primes up to `n` is at least `2 ^ (n / 2)`. This is the lower bound
complement to `primorial_le_four_pow` (which gives the upper bound `n# ≤ 4 ^ n`). -/
theorem two_pow_div_two_le_primorial {n : ℕ} : 2 ^ (n / 2) ≤ n# := by
  obtain hn | hn := le_or_gt 2 n
  · exact (pow_le_pow_right₀ (by lia) (Nat.div_le_div_right (by lia))).trans
      (two_pow_half_succ_le_primorial hn)
  · decide +revert
