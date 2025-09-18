/-
Copyright (c) 2024 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime

/-!
# Factorisation properties of natural numbers

This file defines abundant, pseudoperfect, deficient, and weird numbers and formalizes their
relations with prime and perfect numbers.

## Main Definitions

* `Nat.Abundant`: a natural number `n` is _abundant_ if the sum of its proper divisors is greater
  than `n`
* `Nat.Pseudoperfect`: a natural number `n` is _pseudoperfect_ if the sum of a subset of its proper
  divisors equals `n`
* `Nat.Deficient`: a natural number `n` is _deficient_ if the sum of its proper divisors is less
  than `n`
* `Nat.Weird`: a natural number is _weird_ if it is abundant but not pseudoperfect

## Main Results

* `Nat.deficient_or_perfect_or_abundant`: A positive natural number is either deficient,
  perfect, or abundant.
* `Nat.Prime.deficient`: All prime natural numbers are deficient.
* `Nat.infinite_deficient`: There are infinitely many deficient numbers.
* `Nat.Prime.deficient_pow`: Any natural number power of a prime is deficient.

## Implementation Notes
* Zero is not included in any of the definitions and these definitions only apply to natural
  numbers greater than zero.

## References
* [R. W. Prielipp, *PERFECT NUMBERS, ABUNDANT NUMBERS, AND DEFICIENT NUMBERS*][Prielipp1970]

## Tags

abundant, deficient, weird, pseudoperfect
-/

open Finset

namespace Nat

variable {n m p : ℕ}

/-- `n : ℕ` is _abundant_ if the sum of the proper divisors of `n` is greater than `n`. -/
def Abundant (n : ℕ) : Prop := n < ∑ i ∈ properDivisors n, i

/-- `n : ℕ` is _deficient_ if the sum of the proper divisors of `n` is less than `n`. -/
def Deficient (n : ℕ) : Prop := ∑ i ∈ properDivisors n, i < n

/-- A positive natural number `n` is _pseudoperfect_ if there exists a subset of the proper
  divisors of `n` such that the sum of that subset is equal to `n`. -/
def Pseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ s ⊆ properDivisors n, ∑ i ∈ s, i = n

/-- `n : ℕ` is a _weird_ number if and only if it is abundant but not pseudoperfect. -/
def Weird (n : ℕ) : Prop := Abundant n ∧ ¬ Pseudoperfect n

theorem not_pseudoperfect_iff_forall :
    ¬ Pseudoperfect n ↔ n = 0 ∨ ∀ s ⊆ properDivisors n, ∑ i ∈ s, i ≠ n := by
  rw [Pseudoperfect, not_and_or]
  simp only [not_lt, nonpos_iff_eq_zero, not_exists, not_and, ne_eq]

theorem deficient_one : Deficient 1 := zero_lt_one
theorem deficient_two : Deficient 2 := one_lt_two
theorem deficient_three : Deficient 3 := by norm_num [Deficient]

theorem abundant_twelve : Abundant 12 := by
  rw [Abundant, show properDivisors 12 = {1,2,3,4,6} by rfl]
  norm_num

theorem weird_seventy : Weird 70 := by
  rw [Weird, Abundant, not_pseudoperfect_iff_forall]
  have h : properDivisors 70 = {1, 2, 5, 7, 10, 14, 35} := by rfl
  constructor
  · rw [h]
    repeat norm_num
  · rw [h]
    right
    intro s hs
    have hs' := mem_powerset.mpr hs
    fin_cases hs' <;> decide

lemma deficient_iff_not_abundant_and_not_perfect (hn : n ≠ 0) :
    Deficient n ↔ ¬ Abundant n ∧ ¬ Perfect n := by
  dsimp only [Perfect, Abundant, Deficient]
  omega

lemma perfect_iff_not_abundant_and_not_deficient (hn : 0 ≠ n) :
    Perfect n ↔ ¬ Abundant n ∧ ¬ Deficient n := by
  dsimp only [Perfect, Abundant, Deficient]
  omega

lemma abundant_iff_not_perfect_and_not_deficient (hn : 0 ≠ n) :
    Abundant n ↔ ¬ Perfect n ∧ ¬ Deficient n := by
  dsimp only [Perfect, Abundant, Deficient]
  omega

/-- A positive natural number is either deficient, perfect, or abundant -/
theorem deficient_or_perfect_or_abundant (hn : 0 ≠ n) :
    Deficient n ∨ Abundant n ∨ Perfect n := by
  dsimp only [Perfect, Abundant, Deficient]
  omega

theorem Perfect.pseudoperfect (h : Perfect n) : Pseudoperfect n :=
  ⟨h.2, ⟨properDivisors n, ⟨fun ⦃_⦄ a ↦ a, h.1⟩⟩⟩

theorem Prime.not_abundant (h : Prime n) : ¬ Abundant n :=
  fun h1 ↦ (h.one_lt.trans h1).ne' (sum_properDivisors_eq_one_iff_prime.mpr h)

theorem Prime.not_weird (h : Prime n) : ¬ Weird n := by
  simp only [Nat.Weird, not_and_or]
  left
  exact h.not_abundant

theorem Prime.not_pseudoperfect (h : Prime p) : ¬ Pseudoperfect p := by
  simp_rw [not_pseudoperfect_iff_forall, ← mem_powerset,
    show p.properDivisors.powerset = {∅, {1}} by rw [Prime.properDivisors h]; rfl]
  refine Or.inr (fun s hs ↦ ?_)
  fin_cases hs <;>
  simp only [sum_empty, sum_singleton] <;>
  linarith [Prime.one_lt h]

theorem Prime.not_perfect (h : Prime p) : ¬ Perfect p := by
  have h1 := Prime.not_pseudoperfect h
  revert h1
  exact not_imp_not.mpr (Perfect.pseudoperfect)

/-- Any natural number power of a prime is deficient -/
theorem Prime.deficient_pow (h : Prime n) : Deficient (n ^ m) := by
  rcases Nat.eq_zero_or_pos m with (rfl | _)
  · simpa using deficient_one
  · have h1 : (n ^ m).properDivisors = image (n ^ ·) (range m) := by
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
    have h2 : ∑ i ∈ image (fun x => n ^ x) (range m), i = ∑ i ∈ range m, n^i := by
      rw [Finset.sum_image]
      rintro x _ y _
      apply pow_injective_of_not_isUnit h.not_isUnit <| Prime.ne_zero h
    rw [Deficient, h1, h2]
    calc
      ∑ i ∈ range m, n ^ i
        = (n ^ m - 1) / (n - 1) := (Nat.geomSum_eq (Prime.two_le h) _)
      _ ≤ (n ^ m - 1) := Nat.div_le_self (n ^ m - 1) (n - 1)
      _ < n ^ m := sub_lt (pow_pos (Prime.pos h) m) (Nat.one_pos)

theorem _root_.IsPrimePow.deficient (h : IsPrimePow n) : Deficient n := by
  obtain ⟨p, k, hp, -, rfl⟩ := h
  exact hp.nat_prime.deficient_pow

theorem Prime.deficient (h : Prime n) : Deficient n := by
  rw [← pow_one n]
  exact h.deficient_pow

/-- There exists infinitely many deficient numbers -/
theorem infinite_deficient : {n : ℕ | n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  obtain ⟨b, h1, h2⟩ := exists_infinite_primes a.succ
  exact ⟨b, h2.deficient, h1⟩

theorem infinite_even_deficient : {n : ℕ | Even n ∧ n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  use 2 ^ (n + 1)
  constructor
  · exact ⟨⟨2 ^ n, by rw [pow_succ, mul_two]⟩, prime_two.deficient_pow⟩
  · calc
      n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
      _ < 2 ^ (n + 1) := (Nat.pow_lt_pow_iff_right (Nat.one_lt_two)).mpr (lt_add_one n)

theorem infinite_odd_deficient : {n : ℕ | Odd n ∧ n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, ⟨_, h2⟩⟩ := exists_infinite_primes (max (n + 1) 3)
  exact ⟨p, Set.mem_setOf.mpr ⟨Prime.odd_of_ne_two h2 (Ne.symm (ne_of_lt (by omega))),
    Prime.deficient h2⟩, by omega⟩

end Nat
