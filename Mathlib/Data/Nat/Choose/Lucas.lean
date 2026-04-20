/-
Copyright (c) 2023 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Basic
meta import Mathlib.Tactic.GRewrite

/-!
# Lucas's theorem

This file contains a proof of [Lucas's theorem](https://en.wikipedia.org/wiki/Lucas's_theorem) about
binomial coefficients, which says that for primes `p`, `n` choose `k` is congruent to product of
`n_i` choose `k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`,
respectively.

## Main statements

* `lucas_theorem`: the binomial coefficient `n choose k` is congruent to the product of `n_i choose
  k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`, respectively.
-/

public section

open Finset hiding choose

open Nat Polynomial

namespace Choose

variable {n k a b p : ℕ} [hp : Fact p.Prime]

/-- For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) * choose (n / p) (k / p)`
modulo `p`. Also see `choose_modEq_choose_mod_mul_choose_div_nat` for the version with `MOD`. -/
theorem choose_modEq_choose_mod_mul_choose_div :
    choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZMOD p] := by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    simpa using add_pow_eq_mul_pow_add_pow_div_char (X : (ZMod p)[X]) 1 p _
  simp only [← ZMod.intCast_eq_intCast_iff,
    ← coeff_X_add_one_pow _ n k, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, map_X, decompose]
  simp only [add_pow, one_pow, mul_one, ← pow_mul, sum_mul_sum]
  conv_lhs =>
    enter [1, 2, k, 2, k']
    rw [← mul_assoc, mul_right_comm _ _ (X ^ (p * k')), ← pow_add, mul_assoc, ← cast_mul]
  have h_iff : ∀ x ∈ range (n % p + 1) ×ˢ range (n / p + 1),
      k = x.1 + p * x.2 ↔ (k % p, k / p) = x := by
    intro ⟨x₁, x₂⟩ hx
    rw [Prod.mk.injEq]
    constructor <;> intro h
    · simp only [mem_product, mem_range] at hx
      have h' : x₁ < p := lt_of_lt_of_le hx.left <| mod_lt _ Fin.pos'
      rw [h, add_mul_mod_self_left, add_mul_div_left _ _ Fin.pos', eq_comm (b := x₂)]
      exact ⟨mod_eq_of_lt h', right_eq_add.mpr (div_eq_of_lt h')⟩
    · rw [← h.left, ← h.right, mod_add_div]
  simp only [finset_sum_coeff, coeff_mul_natCast, coeff_X_pow, ite_mul, zero_mul, ← cast_mul]
  rw [← sum_product', sum_congr rfl (fun a ha ↦ if_congr (h_iff a ha) rfl rfl), sum_ite_eq]
  split_ifs with h
  · simp
  · rw [mem_product, mem_range, mem_range, not_and_or, Nat.lt_succ_iff, not_le, not_lt] at h
    cases h <;> simp [choose_eq_zero_of_lt (by tauto)]

/-- For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) * choose (n / p) (k / p)`
modulo `p`. Also see `choose_modEq_choose_mod_mul_choose_div` for the version with `ZMOD`. -/
theorem choose_modEq_choose_mod_mul_choose_div_nat :
    choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_choose_mod_mul_choose_div

/-- For primes `p`, `choose n k` is congruent to the product of `choose (⌊n / p ^ i⌋ % p)
(⌊k / p ^ i⌋ % p)` over i < a, multiplied by `choose (⌊n / p ^ a⌋) (⌊k / p ^ a⌋)`, modulo `p`. -/
theorem choose_modEq_choose_mul_prod_range_choose (a : ℕ) :
    choose n k ≡ choose (n / p ^ a) (k / p ^ a) *
      ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] :=
  match a with
  | Nat.zero => by simp
  | Nat.succ a => (choose_modEq_choose_mul_prod_range_choose a).trans <| by
    rw [prod_range_succ, cast_mul, ← mul_assoc, mul_right_comm]
    gcongr
    apply choose_modEq_choose_mod_mul_choose_div.trans
    simp_rw [pow_succ, Nat.div_div_eq_div_mul, mul_comm, Int.ModEq.refl]

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`. -/
theorem choose_modEq_prod_range_choose {a : ℕ} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] := by
  apply (choose_modEq_choose_mul_prod_range_choose a).trans
  simp_rw [Nat.div_eq_of_lt ha₁, Nat.div_eq_of_lt ha₂, choose, cast_one, one_mul, cast_prod,
    Int.ModEq.refl]

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`. -/
theorem choose_modEq_prod_range_choose_nat {a : ℕ} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_prod_range_choose ha₁ ha₂

alias lucas_theorem := choose_modEq_prod_range_choose
alias lucas_theorem_nat := choose_modEq_prod_range_choose_nat

/-- For primes `p`, `choose (p * a) (p * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_mul_mul_modEq_choose_nat` for the version with `MOD`. -/
theorem choose_mul_mul_modEq_choose :
    choose (p * a) (p * b) ≡ choose a b [ZMOD p] := by
  grw [choose_modEq_choose_mod_mul_choose_div]
  simp [NeZero.pos, Int.ModEq.refl]

/-- For primes `p`, `choose (p * a) (p * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_mul_mul_modEq_choose` for the version with `ZMOD`. -/
theorem choose_mul_mul_modEq_choose_nat :
    choose (p * a) (p * b) ≡ choose a b [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_mul_mul_modEq_choose

/-- For primes `p`, `choose (p ^ k * a) (p ^ k * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_pow_mul_pow_mul_modEq_choose_nat` for the version with `MOD`. -/
theorem choose_pow_mul_pow_mul_modEq_choose :
    choose (p ^ k * a) (p ^ k * b) ≡ choose a b [ZMOD p] := by
  induction k with
  | zero => simp [Int.ModEq.refl]
  | succ k ih =>
    grw [Nat.pow_succ', mul_assoc, mul_assoc, choose_mul_mul_modEq_choose, ih]

/-- For primes `p`, `choose (p ^ k * a) (p ^ k * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_pow_mul_pow_mul_modEq_choose` for the version with `ZMOD`. -/
theorem choose_pow_mul_pow_mul_modEq_choose_nat :
    choose (p ^ k * a) (p ^ k * b) ≡ choose a b [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_pow_mul_pow_mul_modEq_choose

/-- For primes `p` and positive integer `n`, assume that for all `i ∈ Icc 1 (n - 1)`,
`choose n i` congruent to `0` module `p`, then `n = p ^ multiplicity p n`.
Also see `eq_pow_multiplicity_of_choose_modEq_zero_nat` for the version with `MOD`. -/
theorem eq_pow_multiplicity_of_choose_modEq_zero (hn : 0 < n)
    (h : ∀ i ∈ Icc 1 (n - 1), n.choose i ≡ 0 [ZMOD p]) : n = p ^ multiplicity p n := by
  by_contra! hn₀
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd p n
  specialize h _ (mem_Icc.mpr ⟨NeZero.one_le, le_sub_one_of_lt <| lt_of_le_of_ne (le_of_dvd hn
    (pow_multiplicity_dvd p n)) hn₀.symm⟩)
  nth_grw 1 [← mul_one (p ^ _), hm, choose_pow_mul_pow_mul_modEq_choose, choose_one_right] at h
  have : ¬ p ∣ m := by
    by_contra! hc
    have : p ^ (multiplicity p n + 1) ∣ n := by
      nth_rw 2 [hm]
      simpa using Nat.mul_dvd_mul_left _ hc
    nlinarith [(FiniteMultiplicity.pow_dvd_iff_le_multiplicity (finiteMultiplicity_iff.mpr
      ⟨hp.out.ne_one, hn⟩)).mp this]
  norm_cast at h
  exact absurd (dvd_iff_mod_eq_zero.mpr h) this

/-- For primes `p` and positive integer `n`, assume that for all `i ∈ Icc 1 (n - 1)`,
`choose n i` congruent to `0` module `p`, then `n = p ^ multiplicity p n`.
Also see `eq_pow_multiplicity_of_choose_modEq_zero` for the version with `ZMOD`. -/
theorem eq_pow_multiplicity_of_choose_modEq_zero_nat (hn : 0 < n)
    (h : ∀ i ∈ Icc 1 (n - 1), n.choose i ≡ 0 [MOD p]) : n = p ^ multiplicity p n :=
  eq_pow_multiplicity_of_choose_modEq_zero hn (by exact_mod_cast h)

/-- For a prime power `n`, the minimal prime factor divides the greatest common divisor of
`choose n 1, ⋯, choose n (n - 1)`. -/
theorem minFac_dvd_gcd_choose_of_isPrimePow (h : IsPrimePow n) :
    n.minFac ∣ (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) := by
  obtain ⟨k, _, _, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  exact dvd_gcd_iff.mpr fun i hi => by
    nth_rw 2 [hn₁]
    exact Prime.dvd_choose_pow (minFac_prime_iff.mpr h.ne_one) (by grind) (by grind)

/-- For a prime power `n`, the greatest common divisor of `choose n 1, ⋯, choose n (n - 1)`
is actually the minimal prime factor of `n`. -/
theorem gcd_choose_eq_minFac_of_isPrimePow (h : IsPrimePow n) :
    (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) = n.minFac := by
  have ne_zero : (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) ≠ 0 :=
    Finset.gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  obtain ⟨k, _, k_pos, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  have : ¬ n.minFac ^ 2 ∣ (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) := by
    refine mt Finset.dvd_gcd_iff.mp ?_
    simp only [mem_Icc, not_forall]
    have : n.minFac ^ (k - 1) ≤ n.minFac ^ k := Nat.pow_le_pow_right (minFac_pos n) (sub_le k 1)
    refine ⟨n.minFac ^ (k-1), ⟨one_le_pow _ _ (minFac_pos n), ?_⟩, ?_⟩
    · refine le_sub_one_of_lt ?_
      nth_rw 2 [hn₁]
      exact Nat.pow_lt_pow_of_lt (Prime.one_lt isPrime) (sub_one_lt_of_lt k_pos)
    · refine emultiplicity_lt_iff_not_dvd.mp ?_
      nth_rw 2 [hn₁]
      rw [Nat.Prime.emultiplicity_choose_prime_pow isPrime this (pow_ne_zero _
        (Nat.Prime.ne_zero isPrime)), multiplicity_pow_self_of_prime (prime_iff.mp isPrime)]
      norm_cast
      grind
  have h₁ : ((Icc 1 (n - 1)).gcd fun i ↦ n.choose i).primeFactors = {n.minFac} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨isPrime.mem_primeFactors
      (minFac_dvd_gcd_choose_of_isPrimePow h) ne_zero, ?_⟩
    intro p hp
    simp only [mem_primeFactors, ne_eq] at hp
    obtain ⟨hp₁, hp₂, hp₃⟩ := hp
    simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at hp₂
    have := eq_pow_multiplicity_of_choose_modEq_zero_nat (hp := ⟨hp₁⟩) h.pos hp₂
    have dvd_pow : n.minFac ∣  p ^ multiplicity p n := this ▸ minFac_dvd _
    exact (Nat.prime_dvd_prime_iff_eq isPrime hp₁).mp (isPrime.dvd_of_dvd_pow dvd_pow)|>.symm
  have : multiplicity n.minFac ((Icc 1 (n - 1)).gcd fun i ↦ n.choose i) = 1 := by
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ this
    simpa using minFac_dvd_gcd_choose_of_isPrimePow h
  rw [Nat.prod_pow_primeFactors_factorization ne_zero, h₁]
  simp [← Nat.multiplicity_eq_factorization isPrime ne_zero, this]

/-- For a natural number `n` greater than `1`, assume that `n` is not a prime power, then
the greatest common divisor of  `choose n 1, ⋯, choose n (n - 1)` is `1`. -/
theorem gcd_choose_eq_one_of_not_isPrimePow (hn : 1 < n) (hpn : ¬ IsPrimePow n) :
    (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) = 1 := by
  contrapose! hpn
  obtain ⟨q, hq, h⟩ := Nat.exists_prime_and_dvd hpn
  simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at h
  have := eq_pow_multiplicity_of_choose_modEq_zero_nat (zero_lt_of_lt hn) h (hp := ⟨hq⟩)
  refine (isPrimePow_nat_iff n).mpr ⟨q, _, hq, Dvd.multiplicity_pos ?_, this.symm⟩
  specialize h 1 (by grind)
  rw [choose_one_right, modEq_zero_iff_dvd] at h
  exact h

end Choose
