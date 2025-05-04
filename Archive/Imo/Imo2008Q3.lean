/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.LinearCombination

/-!
# IMO 2008 Q3
Prove that there exist infinitely many positive integers `n` such that `n^2 + 1` has a prime
divisor which is greater than `2n + √(2n)`.

# Solution
We first prove the following lemma: for every prime `p > 20`, satisfying `p ≡ 1 [MOD 4]`,
there exists `n ∈ ℕ` such that `p ∣ n^2 + 1` and `p > 2n + √(2n)`. Then the statement of the
problem follows from the fact that there exist infinitely many primes `p ≡ 1 [MOD 4]`.

To prove the lemma, notice that `p ≡ 1 [MOD 4]` implies `∃ n ∈ ℕ` such that `n^2 ≡ -1 [MOD p]`
and we can take this `n` such that `n ≤ p/2`. Let `k = p - 2n ≥ 0`. Then we have:
`k^2 + 4 = (p - 2n)^2 + 4 ≣ 4n^2 + 4 ≡ 0 [MOD p]`. Then `k^2 + 4 ≥ p` and so `k ≥ √(p - 4) > 4`.
Then `p = 2n + k ≥ 2n + √(p - 4) = 2n + √(2n + k - 4) > √(2n)` and we are done.
-/


open Real

namespace Imo2008Q3

theorem p_lemma (p : ℕ) (hpp : Nat.Prime p) (hp_mod_4_eq_1 : p ≡ 1 [MOD 4]) (hp_gt_20 : p > 20) :
    ∃ n : ℕ, p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + sqrt (2 * n) := by
  haveI := Fact.mk hpp
  have hp_mod_4_ne_3 : p % 4 ≠ 3 := by linarith [show p % 4 = 1 from hp_mod_4_eq_1]
  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr hp_mod_4_ne_3
  let m := ZMod.valMinAbs y
  let n := Int.natAbs m
  have hnat₁ : p ∣ n ^ 2 + 1 := by
    refine Int.natCast_dvd_natCast.mp ?_
    simp only [n, Int.natAbs_sq, Int.natCast_pow, Int.natCast_succ, Int.natCast_dvd_natCast.mp]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (m ^ 2 + 1) p).mp ?_
    simp only [m, Int.cast_pow, Int.cast_add, Int.cast_one, ZMod.coe_valMinAbs]
    rw [pow_two, ← hy]; exact neg_add_cancel 1
  have hnat₂ : n ≤ p / 2 := ZMod.natAbs_valMinAbs_le y
  have hnat₃ : p ≥ 2 * n := by omega
  set k : ℕ := p - 2 * n with hnat₄
  have hnat₅ : p ∣ k ^ 2 + 4 := by
    obtain ⟨x, hx⟩ := hnat₁
    have : (p : ℤ) ∣ (k : ℤ) ^ 2 + 4 := by
      use (p : ℤ) - 4 * n + 4 * x
      have hcast₁ : (k : ℤ) = p - 2 * n := by assumption_mod_cast
      have hcast₂ : (n : ℤ) ^ 2 + 1 = p * x := by assumption_mod_cast
      linear_combination ((k : ℤ) + p - 2 * n) * hcast₁ + 4 * hcast₂
    assumption_mod_cast
  have hnat₆ : k ^ 2 + 4 ≥ p := Nat.le_of_dvd (k ^ 2 + 3).succ_pos hnat₅
  have hreal₁ : (k : ℝ) = p - 2 * n := by assumption_mod_cast
  have hreal₂ : (p : ℝ) > 20 := by assumption_mod_cast
  have hreal₃ : (k : ℝ) ^ 2 + 4 ≥ p := by assumption_mod_cast
  have hreal₅ : (k : ℝ) > 4 := by
    refine lt_of_pow_lt_pow_left₀ 2 k.cast_nonneg ?_
    linarith only [hreal₂, hreal₃]
  have hreal₆ : (k : ℝ) > sqrt (2 * n) := by
    refine lt_of_pow_lt_pow_left₀ 2 k.cast_nonneg ?_
    rw [sq_sqrt (mul_nonneg zero_le_two n.cast_nonneg)]
    linarith only [hreal₁, hreal₃, hreal₅]
  exact ⟨n, hnat₁, by linarith only [hreal₆, hreal₁]⟩

end Imo2008Q3

open Imo2008Q3

theorem imo2008_q3 : ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + sqrt (2 * n) := by
  intro N
  obtain ⟨p, hpp, hineq₁, hpmod4⟩ := Nat.exists_prime_gt_modEq_one (N ^ 2 + 20) four_ne_zero
  obtain ⟨n, hnat, hreal⟩ := p_lemma p hpp hpmod4 (by linarith [hineq₁, Nat.zero_le (N ^ 2)])
  have hineq₂ : n ^ 2 + 1 ≥ p := Nat.le_of_dvd (n ^ 2).succ_pos hnat
  have hineq₃ : n * n ≥ N * N := by linarith [hineq₁, hineq₂]
  have hn_ge_N : n ≥ N := Nat.mul_self_le_mul_self_iff.1 hineq₃
  exact ⟨n, hn_ge_N, p, hpp, hnat, hreal⟩
