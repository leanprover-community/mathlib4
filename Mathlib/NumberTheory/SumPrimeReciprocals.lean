/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.SmoothNumbers

/-!
# The sum of the reciprocals of the primes diverges

We show that the sum of `1/p`, where `p` runs through the prime numbers, diverges.
We follow the elementary proof by Erdős that is reproduced in "Proofs from THE BOOK".
There are two versions of the main result: `not_summable_one_div_on_primes`, which
expresses the sum as a sub-sum of the harmonic series, and `Nat.Primes.not_summable_one_div`,
which writes it as a sum over `Nat.Primes`. We also show that the sum of `p^r` for `r : ℝ`
converges if and only if `r < -1`; see `Nat.Primes.summable_rpow`.

## References

See the sixth proof for the infinity of primes in Chapter 1 of [aigner1999proofs].
The proof is due to Erdős.
-/

open Set Nat
open scoped Topology

/-- The cardinality of the set of `k`-rough numbers `≤ N` is bounded by `N` times the sum
of `1/p` over the primes `k ≤ p ≤ N`. -/
-- This needs `Mathlib/Analysis/RCLike/Basic.lean`, so we put it here
-- instead of in `Mathlib/NumberTheory/SmoothNumbers.lean`.
lemma Nat.roughNumbersUpTo_card_le' (N k : ℕ) :
    (roughNumbersUpTo N k).card ≤
      N * (N.succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 : ℝ) / p) := by
  simp_rw [Finset.mul_sum, mul_one_div]
  exact (Nat.cast_le.mpr <| roughNumbersUpTo_card_le N k).trans <|
    cast_sum (R := ℝ) .. ▸ Finset.sum_le_sum fun n _ ↦ cast_div_le

/-- The sum over primes `k ≤ p ≤ 4^(π(k-1)+1)` over `1/p` (as a real number) is at least `1/2`. -/
lemma one_half_le_sum_primes_ge_one_div (k : ℕ) :
    1 / 2 ≤ ∑ p ∈ (4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow,
      (1 / p : ℝ) := by
  set m : ℕ := 2 ^ k.primesBelow.card
  set N₀ : ℕ := 2 * m ^ 2 with hN₀
  let S : ℝ := ((2 * N₀).succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 / p : ℝ))
  suffices 1 / 2 ≤ S by
    convert this using 5
    rw [show 4 = 2 ^ 2 by simp, pow_right_comm]
    ring
  suffices 2 * N₀ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S by
    rwa [hN₀, ← mul_assoc, ← pow_two 2, ← mul_pow, sqrt_eq', ← sub_le_iff_le_add',
      cast_mul, cast_mul, cast_pow, cast_two,
      show (2 * (2 * m ^ 2) - m * (2 * m) : ℝ) = 2 * (2 * m ^ 2) * (1 / 2) by ring,
      _root_.mul_le_mul_left <| by positivity] at this
  calc (2 * N₀ : ℝ)
    _ = ((2 * N₀).smoothNumbersUpTo k).card + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast ((2 * N₀).smoothNumbersUpTo_card_add_roughNumbersUpTo_card k).symm
    _ ≤ m * (2 * N₀).sqrt + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast Nat.add_le_add_right ((2 * N₀).smoothNumbersUpTo_card_le k) _
    _ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S := add_le_add_left ?_ _
  exact_mod_cast roughNumbersUpTo_card_le' (2 * N₀) k

/-- The sum over the reciprocals of the primes diverges. -/
theorem not_summable_one_div_on_primes :
    ¬ Summable (indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) := by
  intro h
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : ℝ) ∈ 𝓝 0)
  specialize hk ({p | Nat.Prime p} ∩ {p | k ≤ p}) inter_subset_right
  rw [tsum_subtype, indicator_indicator, inter_eq_left.mpr fun n hn ↦ hn.1, mem_Iio] at hk
  have h' : Summable (indicator ({p | Nat.Prime p} ∩ {p | k ≤ p}) fun n ↦ (1 : ℝ) / n) := by
    convert h.indicator {n : ℕ | k ≤ n} using 1
    simp only [indicator_indicator, inter_comm]
  refine ((one_half_le_sum_primes_ge_one_div k).trans_lt <| LE.le.trans_lt ?_ hk).false
  convert Summable.sum_le_tsum (primesBelow ((4 ^ (k.primesBelow.card + 1)).succ) \ primesBelow k)
    (fun n _ ↦ indicator_nonneg (fun p _ ↦ by positivity) _) h' using 2 with p hp
  obtain ⟨hp₁, hp₂⟩ := mem_setOf_eq ▸ Finset.mem_sdiff.mp hp
  have hpp := prime_of_mem_primesBelow hp₁
  refine (indicator_of_mem ?_ fun n : ℕ ↦ (1 / n : ℝ)).symm
  exact ⟨hpp, by simpa [primesBelow, hpp] using hp₂⟩

/-- The sum over the reciprocals of the primes diverges. -/
theorem Nat.Primes.not_summable_one_div : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) := by
  convert summable_subtype_iff_indicator.mp.mt not_summable_one_div_on_primes

/-- The series over `p^r` for primes `p` converges if and only if `r < -1`. -/
theorem Nat.Primes.summable_rpow {r : ℝ} :
    Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ r) ↔ r < -1 := by
  by_cases h : r < -1
  · -- case `r < -1`
    simp only [h, iff_true]
    exact (Real.summable_nat_rpow.mpr h).subtype _
  · -- case `-1 ≤ r`
    simp only [h, iff_false]
    refine fun H ↦ Nat.Primes.not_summable_one_div <| H.of_nonneg_of_le (fun _ ↦ by positivity) ?_
    intro p
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) <| not_lt.mp h
