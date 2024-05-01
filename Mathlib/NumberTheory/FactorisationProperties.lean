/-
Copyright (c) 2024 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic.FinCases

/-!
## Factorisation properties of natural numbers
This file defines abundant, pseudoperfect, deficient, and weird numbers and formalizes their
  relations with prime and perfect numbers.

## Main Definitions
* `Nat.Abundant`: a natural number `n` is abundant if the sum of its proper divisors are greater
  than itself
* `Nat.Pseudoperfect`: a natural number `n` is pseudoperfect if a subset of its proper divisors
  equals itself and it is greater than zero
* `Nat.Deficient`: a natural number `n` is deficient if the sum of its proper divisors is less than
  itself
* `Nat.WeirdNumber`: a natural number is weird if it is both abundant and not pseudoperfect

## Main Results
* `Nat.deficient_or_perfect_or_abundant`: for 0 < `n:ℕ` it is either deficient, perfect, or
  abundant
* `Nat.prime_deficient`: all prime natural numbers are deficient
* `Nat.exists_infinite_deficients`: there are infinite deficient numbers
* `Nat.prime_pow_deficient`: any natural number power of a prime is deficient

## Implementation Details
* Zero is not included in any of the definitions and these definitions only apply to natural
  numbers greater than zero.

## References
* Prielipp, Robert W. “PERFECT NUMBERS, ABUNDANT NUMBERS, AND DEFICIENT NUMBERS.”
  The Mathematics Teacher, vol. 63, no. 8, 1970, pp. 692–96. JSTOR,
  http://www.jstor.org/stable/27958492. Accessed 21 Feb. 2024.

## Tags

abundant, deficient, weird, pseudoperfect
-/

open Nat BigOperators Finset

namespace Nat

variable (n m k : ℕ)

/-- `n : ℕ` is Abundant if and only if the sum of the proper divisors of `n` is greater than `n`-/
def Abundant (n : ℕ) : Prop := ∑ i in properDivisors n, i > n

/--  `n : ℕ` is Deficient if and only if the sum of the proper divisors of `n` is less than `n`-/
def Deficient (n : ℕ) : Prop := ∑ i in properDivisors n, i < n

/-- `n : ℕ` is Pseudoperfect if and only if there exists a subset of the proper divisors of n such
  that the sum of that subset is equal to `n` and `n` is positive -/
def Pseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ s : Finset ℕ, s ∈ powerset (properDivisors n) ∧ ∑ i in s, i = n

/-- `n : ℕ` is a weird number if and only if it is both abundant and pseudoperfect -/
def WeirdNumber (n : ℕ) : Prop := Abundant n ∧ ¬ Pseudoperfect n

theorem not_pseudoperfect_iff_forall :
    ¬ Pseudoperfect n ↔ n = 0 ∨ ∀ (s : Finset ℕ), s ∈ powerset (properDivisors n)
      → ∑ i in s, i ≠ n := by
    have hn : (¬ 0 < n) ↔ n = 0 := by simp only [not_lt, nonpos_iff_eq_zero]
    dsimp only [Pseudoperfect]
    rw [not_and_or, not_exists, hn]
    constructor
    · rintro (h1 | h2)
      · tauto
      · right
        intro s
        have hs : ¬(s ∈ powerset (properDivisors n) ∧ ∑ i in s, i = n) := h2 s
        rw [not_and] at hs
        exact hs
    · rintro (h1 | h2)
      · tauto
      · right
        simp_rw [not_and]
        exact h2

theorem one_deficient : Deficient 1 := by
  dsimp only [Deficient]
  norm_num

theorem two_deficient : Deficient 2 := by
  dsimp only [Nat.Deficient]
  norm_num

theorem three_deficient : Deficient 3 := by
  dsimp only [Deficient]
  norm_num

theorem six_perfect : Perfect 6 := by
  dsimp only [Perfect]
  rw [show properDivisors 6 = {1, 2, 3} by rfl]
  norm_num

theorem twelve_abundant : Abundant 12 := by
  dsimp only [Abundant]
  rw [show properDivisors 12 = {1,2,3,4,6} by rfl]
  norm_num

set_option maxRecDepth 2000 in
theorem seventy_weird : WeirdNumber 70 := by
  dsimp only [WeirdNumber, Abundant]
  rw [not_pseudoperfect_iff_forall]
  have div70 : properDivisors 70 = {1, 2, 5, 7, 10, 14, 35} := by rfl
  constructor
  · rw [div70]
    repeat norm_num
  · rw [div70]
    right
    intro s hs
    fin_cases hs <;> decide

lemma deficient_not_abundant_or_perfect (hn : 0 < n) :
    Deficient n ↔ ¬ Abundant n ∧ ¬ Perfect n := by
      dsimp only [Perfect, Abundant, Deficient]
      omega

lemma perfect_not_abundant_or_deficient (hn : 0 < n) :
    Perfect n ↔ ¬ Abundant n ∧ ¬ Deficient n := by
      dsimp only [Perfect, Abundant, Deficient]
      omega

lemma abundant_not_perfect_or_deficient (hn : 0 < n) :
    Abundant n ↔ ¬ Perfect n ∧ ¬ Deficient n := by
      dsimp only [Perfect, Abundant, Deficient]
      omega

/- All numbers are either deficient, perfect, or abundant -/
theorem deficient_or_perfect_or_abundant (hn : 0 < n) :
    Deficient n ∨ Abundant n ∨ Perfect n := by
      dsimp only [Perfect, Abundant, Deficient]
      omega

theorem perfect_pseudoperfect (h : Perfect n) : Pseudoperfect n := by
  rcases h with ⟨h1, h2⟩
  constructor
  · exact h2
  · use properDivisors n
    exact ⟨mem_powerset_self (properDivisors n), h1⟩

theorem prime_not_abundant (h : Prime n) : ¬ Abundant n := by
  intro h1
  have h2 := sum_properDivisors_eq_one_iff_prime.mpr h
  have h3 := Nat.lt_trans (Prime.one_lt h) h1
  omega

theorem prime_not_weird (h : Prime n) : ¬ WeirdNumber n := by
  simp only [Nat.WeirdNumber, not_and_or]
  left
  exact prime_not_abundant n h

theorem not_pseudoperfect_not_perfect (h : ¬ Pseudoperfect n) : ¬ Perfect n := by
  revert h
  rw [not_imp_not]
  exact perfect_pseudoperfect n

theorem prime_not_pseudoperfect (h : Nat.Prime n) : ¬ Nat.Pseudoperfect n := by
  rw [not_pseudoperfect_iff_forall]
  have h1 : powerset (properDivisors n) = {∅, {1}} := by
    rw [Prime.properDivisors h]
    exact rfl
  rw [h1]
  right
  rintro s hs
  rcases (List.mem_pair.mp hs) with hs | hs <;>
  {simp only [ne_eq, hs, sum_empty, sum_singleton]; exact Nat.ne_of_lt (by linarith [Prime.one_lt h])}

theorem prime_not_perfect (h : Prime n) : ¬ Perfect n :=
  not_pseudoperfect_not_perfect n (prime_not_pseudoperfect n h)

theorem prime_deficient (h : Prime n) : Deficient n := by
  rw [deficient_not_abundant_or_perfect n]
  · exact ⟨prime_not_abundant n h, prime_not_perfect n h⟩
  · exact Prime.pos h

/-There exists infinite deficient numbers-/
theorem exists_infinite_deficients : ∃ d, n ≤ d ∧ Deficient d := by
  obtain ⟨p, ⟨h1, h2⟩⟩ := exists_infinite_primes n
  have Deficientp : Deficient p :=  prime_deficient p h2
  use p

/-Any natural number power of a prime is deficient-/
theorem prime_pow_deficient (h : Prime n) : Deficient (n^m) := by
  obtain hL | hR := Nat.eq_zero_or_pos m
  · rw [hL, Nat.pow_zero]
    exact le.refl
  · have n_gtOne : 1 < n := Prime.two_le h
    have hp : properDivisors (n ^ m) = image (n ^ ·) (range m) := by
      apply subset_antisymm <;> intro a
      · simp only [mem_properDivisors, mem_image, mem_range, dvd_prime_pow h]
        rintro ⟨⟨t, ht, rfl⟩, ha'⟩
        exact ⟨t, lt_of_le_of_ne ht (fun ht' ↦ lt_irrefl _ (ht' ▸ ha')), rfl⟩
      · simp only [mem_image, mem_range, mem_properDivisors, forall_exists_index, and_imp]
        intro x hx hy
        constructor
        · rw [← hy, dvd_prime_pow h]
          use x
          exact ⟨Nat.le_of_succ_le hx, rfl⟩
        · rw [← hy]
          exact (Nat.pow_lt_pow_iff_right (Prime.two_le h)).mpr hx
    have hw : ∑ i in image (fun x => n ^ x) (range m), i = ∑ i in range m, n^i := by
      rw [Finset.sum_image]
      rintro x _ y _ hnxy
      by_contra hc
      rcases (Ne.lt_or_lt hc) with hxy1 | hxy2
      · linarith [(pow_lt_pow_iff_right n_gtOne).mpr hxy1]
      · linarith [(pow_lt_pow_iff_right n_gtOne).mpr hxy2]
    have hq : ∑ i in range m, n ^ i = (n ^ m - 1) / (n - 1) := Nat.geomSum_eq (Prime.two_le h) _
    have hr : 1 < n ^ m :=  one_lt_pow (not_eq_zero_of_lt hR) (Prime.two_le h)
    rw [Deficient, hp, hw, hq]
    calc
      (n ^ m - 1) / (n - 1) ≤ (n ^ m - 1) := Nat.div_le_self (n ^ m - 1) (n - 1)
      _                   < n ^ m := by {rw [tsub_lt_self_iff]; norm_num; exact lt_of_succ_lt hr}

theorem exists_infinite_even_deficients : ∃ d, n ≤ d ∧ Deficient d ∧ Even d := by
  use 2 ^ (n + 1)
  constructor
  · rw [Nat.le_iff_lt_or_eq]
    left
    calc
      n ≤ 2 * n := by linarith
      _ < 2 * (2 ^ n) := Nat.mul_lt_mul_of_pos_left (lt_two_pow n) (Nat.zero_lt_two)
      _ = 2 ^ (n + 1) := by rw [Nat.pow_succ']
  · exact ⟨prime_pow_deficient 2 (n + 1) prime_two, even_pow.mpr ⟨even_iff.mpr rfl, succ_ne_zero n⟩⟩

theorem exists_infinite_odd_deficients : ∃ d, n ≤ d ∧ Nat.Deficient d ∧ Odd d := by
  use 3 ^ (n + 1)
  have nlttwo : n < 2 ^ (n + 1) := by
    calc
      n ≤ 2 * n := by linarith
      _ < 2 * (2 ^ n) := mul_lt_mul_of_pos_left (lt_two_pow n) (by linarith)
      _ = 2 ^ (n + 1) := by rw [Nat.pow_succ']
  have twoltthree : 2 ^ (n + 1) ≤ 3 ^ (n + 1) :=
    (Nat.pow_le_pow_iff_left (succ_ne_zero n)).mpr (by norm_num)
  constructor
  · linarith
  · exact ⟨prime_pow_deficient 3 (n + 1) prime_three, Odd.pow (odd_iff.mpr (by rfl))⟩

end Nat
