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
* `Nat.Abundant`: a natural number `n` is _abundant_ if the sum of its proper divisors are greater
  than `n`
* `Nat.Pseudoperfect`: a natural number `n` is _pseudoperfect_ if a subset of its proper divisors
  equals `n`
* `Nat.Deficient`: a natural number `n` is _deficient_ if the sum of its proper divisors is less
  than `n`
* `Nat.WeirdNumber`: a natural number is _weird_ if it is both abundant and not pseudoperfect

## Main Results
* `Nat.deficient_or_perfect_or_abundant`: a positive natural number is either deficient,
  perfect, or abundant
* `Nat.prime_deficient`: all prime natural numbers are deficient
* `Nat.exists_infinite_deficients`: there are infinitely many deficient numbers
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

open BigOperators Finset

namespace Nat

/-- `n : ℕ` is _abundant_ if and only if the sum of the proper divisors of `n` is greater than `n`
  -/
def Abundant (n : ℕ) : Prop := ∑ i in properDivisors n, i > n

/-- `n : ℕ` is _deficient_ if and only if the sum of the proper divisors of `n` is less than `n` -/
def Deficient (n : ℕ) : Prop := ∑ i in properDivisors n, i < n

/-- `n : ℕ` is _pseudoperfect_ if and only if there exists a subset of the proper divisors of n
  such that the sum of that subset is equal to `n` and `n` is positive -/
def Pseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ s : Finset ℕ, s ∈ powerset (properDivisors n) ∧ ∑ i in s, i = n

/-- `n : ℕ` is a _weird_ number if and only if it is both abundant and pseudoperfect -/
def WeirdNumber (n : ℕ) : Prop := Abundant n ∧ ¬ Pseudoperfect n

theorem not_pseudoperfect_iff_forall :
    ¬ Pseudoperfect n ↔ n = 0 ∨ ∀ (s : Finset ℕ), s ∈ powerset (properDivisors n)
      → ∑ i in s, i ≠ n := by
    rw [Pseudoperfect, not_and_or]
    simp only [not_lt, nonpos_iff_eq_zero, mem_powerset, not_exists, not_and, ne_eq]

theorem one_deficient : Deficient 1 := le.refl

theorem two_deficient : Deficient 2 := le.refl

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

/-- A positive natural number is either deficient, perfect, or abundant -/
theorem deficient_or_perfect_or_abundant (hn : 0 < n) :
    Deficient n ∨ Abundant n ∨ Perfect n := by
    dsimp only [Perfect, Abundant, Deficient]
    omega

theorem perfect_pseudoperfect (h : Perfect n) : Pseudoperfect n :=
  ⟨h.2, _, mem_powerset_self _, h.1⟩

theorem prime_not_abundant (h : Prime n) : ¬ Abundant n :=
  fun h1 ↦ (h.one_lt.trans h1).ne' (sum_properDivisors_eq_one_iff_prime.mpr h)

theorem prime_not_weird (h : Prime n) : ¬ WeirdNumber n := by
  simp only [Nat.WeirdNumber, not_and_or]
  left
  exact prime_not_abundant h

theorem prime_not_pseudoperfect (h : Nat.Prime n) : ¬ Nat.Pseudoperfect n := by
  rw [not_pseudoperfect_iff_forall,
    show powerset (properDivisors n) = {∅, {1}} by rw [Prime.properDivisors h]; rfl]
  refine Or.inr (fun s hs ↦ ?_)
  fin_cases hs <;>
  simp only [sum_empty, sum_singleton] <;>
  linarith [Prime.one_lt h]

theorem prime_not_perfect (h : Prime n) : ¬ Perfect n := by
  have h1 := prime_not_pseudoperfect h
  revert h1
  exact not_imp_not.mpr (perfect_pseudoperfect)

/-- Any natural number power of a prime is deficient -/
theorem prime_pow_deficient (h : Prime n) : Deficient (n ^ m) := by
  rcases Nat.eq_zero_or_pos m with (hL | _)
  · rw [hL, Nat.pow_zero]
    exact one_deficient
  · have h1 : properDivisors (n ^ m) = image (n ^ ·) (range m) := by
      apply subset_antisymm <;> intro a
      · simp only [mem_properDivisors, mem_image, mem_range, dvd_prime_pow h]
        rintro ⟨⟨t, ht, rfl⟩, ha'⟩
        exact ⟨t, lt_of_le_of_ne ht (fun ht' ↦ lt_irrefl _ (ht' ▸ ha')), rfl⟩
      · simp only [mem_image, mem_range, mem_properDivisors, forall_exists_index, and_imp]
        intro x hx hy
        constructor
        · rw [← hy, dvd_prime_pow h]
          exact ⟨x, Nat.le_of_succ_le hx, rfl⟩
        · rw [← hy]
          exact (Nat.pow_lt_pow_iff_right (Prime.two_le h)).mpr hx
    have h2 : ∑ i in image (fun x => n ^ x) (range m), i = ∑ i in range m, n^i := by
      rw [Finset.sum_image]
      rintro x _ y _ hnxy
      by_contra hc
      rcases (Ne.lt_or_lt hc) with hx | hx <;>
      linarith [(pow_lt_pow_iff_right (Prime.one_lt h)).mpr hx]
    rw [Deficient, h1, h2]
    calc
      ∑ i ∈ range m, n ^ i
        = (n ^ m - 1) / (n - 1) := (Nat.geomSum_eq (Prime.two_le h) _)
      _ ≤ (n ^ m - 1) := Nat.div_le_self (n ^ m - 1) (n - 1)
      _ < n ^ m := sub_lt (pow_pos (Prime.pos h) m) (Nat.one_pos)

theorem prime_deficient (h : Prime n) : Deficient n := by
  rw [← pow_one n]
  exact prime_pow_deficient h

/-- There exists infinitely many deficient numbers -/
theorem exists_infinite_deficients : ∃ d, n ≤ d ∧ Deficient d := by
  obtain ⟨p, ⟨h1, h2⟩⟩ := exists_infinite_primes n
  exact ⟨p, h1, prime_deficient h2⟩

theorem exists_infinite_even_deficients : ∃ d, n ≤ d ∧ Deficient d ∧ Even d := by
  use 2 ^ (n + 1)
  constructor
  · calc
      n ≤ 2 ^ n := Nat.le_of_lt (lt_two_pow n)
      _ ≤ 2 ^ (n + 1) := le_of_succ_le ((Nat.pow_lt_pow_iff_right (Nat.one_lt_two)).mpr
        (lt_add_one n))
  · exact ⟨prime_pow_deficient prime_two, even_pow.mpr ⟨even_two, Ne.symm
      (NeZero.ne' (n + 1))⟩⟩

theorem exists_infinite_odd_deficients : ∃ d, n ≤ d ∧ Nat.Deficient d ∧ Odd d := by
  use 3 ^ (n + 1)
  have h : n < 3 ^ (n + 1):= by
    calc
      n < 2 ^ n := lt_two_pow n
      _ < 2 ^ (n + 1) := pow_lt_pow_right Nat.one_lt_two (lt_add_one n)
      _ < 3 ^ (n + 1) := Nat.pow_lt_pow_left (by norm_num) (Ne.symm (NeZero.ne' (n + 1)))
  exact ⟨le_of_succ_le h, ⟨prime_pow_deficient prime_three, Odd.pow (odd_iff.mpr
    (by rfl))⟩⟩

end Nat
