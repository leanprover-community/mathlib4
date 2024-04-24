/-
Copyright (c) 2024 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Colin Jones
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Analysis.Normed.Field.Basic

/-!
## FactorisationProperties.lean
This file defines abundant, semi-perfect, deficient, and weird numbers and formalizes their
  relations with prime and perfect numbers.

## Main Definitions
Let `n : ℕ`. All the following definitions are in the Nat namespace.
* `Abundant` a natural number `n` is abundant if the sum of its proper divisors are greater than
  itself and it is greater than zero
* `Pseudoperfect` a natural number `n` is semi-perfect if a subset of its proper divisors equals
  itself and it is greater than zero
* `Deficient` a natural number `n` is deficient if the sum of its proper divisors is less than
  itself and it is greater than zero
* `WeirdNumber` a natural number is weird if it is both abundant and not semi-perfect

## Main Results
* `divisors_eq_proper_union_self` the `Finset` that is `Nat.divisors` is equal to the union of
  `Nat.properDivisors` and the number itself
* `deficient_or_perfect_or_abundant` any natural number greater than zero is either deficient,
  perfect, or abundant
* `prime_deficient` all prime natural numbers are deficient
* `prime_pow_deficient` any power of a prime number is deficient

## Implementation Details
* Zero is not included in any of the definitions and these definitions only apply to natural
  numbers greater than zero.

## References
* Prielipp, Robert W. “PERFECT NUMBERS, ABUNDANT NUMBERS, AND DEFICIENT NUMBERS.”
  The Mathematics Teacher, vol. 63, no. 8, 1970, pp. 692–96. JSTOR,
  http://www.jstor.org/stable/27958492. Accessed 21 Feb. 2024.

## Tags
abundant deficient weird Pseudoperfect

-/

open Nat BigOperators Finset

set_option maxRecDepth 1000000

namespace Nat

variable (n m k : ℕ)

/-- `n : ℕ` is Abundant if and only if the sum of the proper divisors of `n` is greater than `n`
  and `n` is positive. -/
def Abundant (n : ℕ) : Prop := ∑ i in properDivisors n, i > n

/--  `n : ℕ` is Deficient if and only if the sum of the proper divisors of `n` is less than `n`
  and `n` is positive -/
def Deficient (n : ℕ) : Prop := ∑ i in properDivisors n, i < n

/-- `n : ℕ` is Pseudoperfect if and only if there exists a subset of the proper divisors of n such
  that the sum of that subset is equal to `n` and `n` is positive -/
def Pseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ s : Finset ℕ, s ∈ powerset (properDivisors n) ∧ ∑ i in s, i = n

/-- `n : ℕ` is a weird number if and only if it is both abundant and semi-perfect -/
def WeirdNumber (n : ℕ) : Prop := Abundant n ∧ ¬ Pseudoperfect n

theorem not_pseudoperfect_iff_forall :
  ¬ Pseudoperfect n ↔ n = 0 ∨ ∀ (s : Finset ℕ), s ∈ powerset (properDivisors n)
    → ∑ i in s, i ≠ n := by
  have hn : (¬ 0 < n) ↔ n = 0 := by simp only [not_lt, nonpos_iff_eq_zero]
  dsimp [Pseudoperfect]
  rw [not_and_or, not_exists, hn]
  constructor
  · rintro (h1 | h2)
    · tauto
    · right
      intro s
      have hs : ¬(s ∈ powerset (properDivisors n) ∧ ∑ i in s, i = n) := by exact h2 s
      rw [not_and] at hs
      exact hs
  · rintro (h1 | h2)
    · tauto
    · right
      simp_rw [not_and]
      exact h2

theorem one_deficient : Nat.Deficient 1 := by
  dsimp [Nat.Deficient]
  norm_num

theorem two_deficient : Nat.Deficient 2 := by
  dsimp [Nat.Deficient]
  norm_num

theorem three_deficient : Nat.Deficient 3 := by
  dsimp [Nat.Deficient]
  norm_num

theorem six_perfect : Nat.Perfect 6 := by
  dsimp [Nat.Perfect]
  rw [show properDivisors 6 = {1, 2, 3} by rfl]
  norm_num

theorem twelve_abundant : Nat.Abundant 12 := by
  dsimp [Nat.Abundant]
  rw [show properDivisors 12 = {1,2,3,4,6} by rfl]
  norm_num

theorem seventy_weird : Nat.WeirdNumber 70 := by
  dsimp [Nat.WeirdNumber, Nat.Abundant]
  rw [not_pseudoperfect_iff_forall]
  have div70 : properDivisors 70 = {1, 2, 5, 7, 10, 14, 35} := by rfl
  constructor
  · rw [div70]
    repeat norm_num
  · rw [div70]
    right
    intro s hs
    fin_cases hs <;> decide

theorem divisor_subseteq_mul (hn : 0 < n) (hm : 0 < m) :
    divisors n ∪ divisors m ⊆ divisors (n * m) := by
  intro a ha
  simp only [mem_union, mem_divisors] at ha ⊢
  rcases ha with hn1 | hm1
  · exact ⟨dvd_trans hn1.1 ⟨m, rfl⟩, by positivity⟩
  · exact ⟨dvd_trans hm1.1 ⟨n, mul_comm ..⟩, by positivity⟩

theorem prop_divisors_subseteq_mul (hn : 0 < n) (hm : 0 < m) :
  Nat.properDivisors n ∪ Nat.properDivisors m ⊆ Nat.properDivisors (n*m) := by
  refine subset_iff.mpr ?_
  rintro a ha
  have ha' : a ∈ properDivisors n ∨ a ∈ properDivisors m := by
    simp_all only [gt_iff_lt, le_mul_iff_one_le_right,
      le_mul_iff_one_le_left, mem_union, mem_properDivisors]
  rcases ha' with hn1 | hm1
  · have han : a ∣ n := by
      simp_all only [mem_properDivisors, and_self]
    refine mem_properDivisors.mpr ?_
    constructor
    exact Dvd.dvd.mul_right han m
    refine lt_mul_of_lt_of_one_le ?_ hm
    simp_all only [gt_iff_lt, le_mul_iff_one_le_right, mem_properDivisors, true_and, ne_eq]
  · have ham : a ∣ m := by
      simp_all only [gt_iff_lt, le_mul_iff_one_le_right, mem_properDivisors]
    refine mem_properDivisors.mpr ?_
    constructor
    exact Dvd.dvd.mul_left ham n
    refine lt_mul_of_one_le_of_lt hn ?_
    simp_all only [gt_iff_lt, le_mul_iff_one_le_right, le_mul_iff_one_le_left, mem_properDivisors,
       true_and, ne_eq]

lemma divisors_eq_proper_union_self (hn : 0 < n) :
  Nat.divisors n = Nat.properDivisors n ∪ {n} := by
    dsimp [divisors, properDivisors]
    ext a
    simp [*]
    constructor
    <;> rintro ⟨⟨h1, h2⟩, h3⟩
    · omega
    · omega
    · simp only [*, lt_add_iff_pos_right, zero_lt_one, and_true, dvd_refl]
      omega

lemma deficient_not_abundant_or_perfect (hn : 0 < n) :
  Deficient n ↔ ¬ Abundant n ∧ ¬ Perfect n := by
    dsimp [Perfect, Abundant, Deficient]
    omega

lemma perfect_not_abundant_or_deficient (hn : 0 < n) :
  Perfect n ↔ ¬ Abundant n ∧ ¬ Deficient n := by
    dsimp [Perfect, Abundant, Deficient]
    omega

lemma abundant_not_perfect_or_deficient (hn : 0 < n) :
  Abundant n ↔ ¬ Perfect n ∧ ¬ Deficient n := by
    dsimp [Perfect, Abundant, Deficient]
    omega

/- All numbers are either deficient, perfect, or abundant -/
theorem deficient_or_perfect_or_abundant (hn : 0 < n) :
  Deficient n ∨ Abundant n ∨ Perfect n := by
    dsimp [Perfect, Abundant, Deficient]
    omega

theorem perfect_pseudoperfect (h : Perfect n) : Pseudoperfect n := by
  rcases h with ⟨h1, h2⟩
  constructor
  · exact h2
  · use properDivisors n
    constructor
    · exact mem_powerset_self (properDivisors n)
    · exact h1

theorem prime_not_abundant (h : Prime n) : ¬ Abundant n := by
  intro h1
  have h2 : ∑ i in properDivisors n, i = 1 := by exact sum_properDivisors_eq_one_iff_prime.mpr h
  have h3 : n > 1 := by exact Prime.one_lt h
  have h4 : ∑ i in properDivisors n, i > 1 := by exact Nat.lt_trans h3 h1
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
  have h2 : n > 1 := by exact Prime.one_lt h
  rw [h1]
  right
  rintro s hs
  have hs' : s = ∅ ∨ s = {1} := by exact List.mem_pair.mp hs
  rcases hs' with hs1 | hs2
  <;> {simp [*]; linarith}

theorem prime_not_perfect (h : Prime n) : ¬ Perfect n := by
  have h1 : ¬ Pseudoperfect n := by apply prime_not_pseudoperfect n h
  exact not_pseudoperfect_not_perfect n h1

theorem prime_deficient (h : Prime n) : Deficient n := by
  refine (deficient_not_abundant_or_perfect n ?hn).mpr ?_
  exact Prime.pos h
  constructor
  · exact prime_not_abundant n h
  · exact prime_not_perfect n h

theorem exists_infinite_deficients : ∃ d, n ≤ d ∧ Deficient d := by
  obtain ⟨p, ⟨h1, h2⟩⟩ := exists_infinite_primes n
  have Deficientp : Deficient p := by exact prime_deficient p h2
  use p

theorem prime_pow_deficient (h : Prime n) : Deficient (n^m) := by
  have m_zeroOrGt : m = 0 ∨ m > 0 := by exact Nat.eq_zero_or_pos m
  obtain hL | hR := m_zeroOrGt
  · rw [hL, Nat.pow_zero]
    exact le.refl
  · have n_geTwo : 2 ≤ n := by exact Prime.two_le h
    have n_gtOne : 1 < n := by exact n_geTwo
    have m_neq_zero : m ≠ 0 := by linarith
    have hp : properDivisors (n^m) = image (n ^ ·) (range m) := by
      have h1 x : x ∣ n ^ m ↔ ∃ k ≤ m, x = n ^ k := by exact dvd_prime_pow h
      have h2 k : n ^ k < n ^ m ↔ k < m := by exact Nat.pow_lt_pow_iff_right n_geTwo
      apply subset_antisymm <;> intro a
      · aesop
      · simp_all [mem_image, mem_range, mem_properDivisors, forall_exists_index, and_imp]
        intro x hx1 hx2
        constructor
        · use x
          constructor
          · exact le_of_succ_le hx1
          · exact id hx2.symm
        · rw [← hx2]
          exact (Nat.pow_lt_pow_iff_right n_geTwo).mpr hx1
    have hw : ∑ i in image (fun x => n ^ x) (range m), i = ∑ i in range m, n^i := by
      rw [Finset.sum_image]
      rintro x hx y hy hnxy
      by_contra hc
      have hxy : x < y ∨ x > y := by exact Ne.lt_or_lt hc
      rcases hxy with hxy1 | hxy2
      · have hn1 : n^x < n^y := by exact (pow_lt_pow_iff_right n_gtOne).mpr hxy1
        linarith
      · have hn2 : n^x > n^y := by exact (pow_lt_pow_iff_right n_gtOne).mpr hxy2
        linarith
    have hq : ∑ i in range m, n ^ i = (n^m - 1) / (n - 1) := by
      refine Nat.geomSum_eq ?_ _
      exact n_geTwo
    have hr : 1 < n ^ m := by exact one_lt_pow m_neq_zero n_geTwo
    rw [Deficient, hp, hw, hq]
    calc
      (n^m - 1) / (n - 1) ≤ (n^m - 1) := by exact Nat.div_le_self (n ^ m - 1) (n - 1)
      _                   < n^m := by {rw [tsub_lt_self_iff]; norm_num; exact lt_of_succ_lt hr}

theorem exists_infinite_even_deficients : ∃ d, n ≤ d ∧ Deficient d ∧ Even d := by
  use 2^(n+1)
  constructor
  · rw [Nat.le_iff_lt_or_eq]
    left
    calc
      n ≤ 2*n := by linarith
      _ < 2*(2^n) := by rel [show n < 2^n by exact Nat.lt_two_pow n]
      _ = 2^(n+1) := by rw [Nat.pow_succ']
  · constructor
    · refine prime_pow_deficient 2 (n + 1) prime_two
    · refine even_pow.mpr ?h.right.right.a
      constructor
      · exact even_iff.mpr rfl
      · exact succ_ne_zero n

theorem exists_infinite_odd_deficients : ∃ d, n ≤ d ∧ Nat.Deficient d ∧ Odd d := by
  use 3^(n+1)
  have nlttwo : n < 2^(n+1) := by
    calc
    n ≤ 2*n := by linarith
    _ < 2*(2^n) := by rel [show n < 2^n by exact Nat.lt_two_pow n]
    _ = 2^(n+1) := by rw [Nat.pow_succ']
  have twoltthree : 2^(n+1) ≤ 3^(n+1) := by
    refine (Nat.pow_le_pow_iff_left (succ_ne_zero n)).mpr ?_; norm_num
  constructor
  · linarith
  · constructor
    · refine prime_pow_deficient 3 (n + 1) prime_three
    · refine Odd.pow ?_
      exact odd_iff.mpr rfl

end Nat
