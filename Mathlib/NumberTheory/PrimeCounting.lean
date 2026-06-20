/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Ralf Stephan
-/
module

public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.Totient
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Prime Counting Function

In this file we define the prime counting function: the function on natural numbers that returns
the number of primes less than or equal to its input.

## Main Results

The main definitions for this file are

- `Nat.primeCounting`: The prime counting function π
- `Nat.primeCounting'`: π(n - 1)
- `Nat.primesBelow`: The finset of primes less than n
  (this was previously in `Mathlib.NumberTheory.SmoothNumbers`)
- `Nat.primesLE`: The finset of primes less than or equal to n

We then prove that these are monotone in `Nat.monotone_primeCounting` and
`Nat.monotone_primeCounting'`. The last main theorem `Nat.primeCounting'_add_le` is an upper
bound on `π'` which arises by observing that all numbers greater than `k` and not coprime to `k`
are not prime, and so only at most `φ(k)/k` fraction of the numbers from `k` to `n` are prime.

## Notation

With `open scoped Nat.Prime`, we use the standard notation `π` to represent the prime counting
function (and `π'` to represent the reindexed version).

-/

@[expose] public section


namespace Nat

open Finset

/-- A variant of the traditional prime counting function which gives the number of primes
*strictly* less than the input. More convenient for avoiding off-by-one errors.

With `open scoped Nat.Prime`, this has notation `π'`. -/
def primeCounting' : ℕ → ℕ := count Prime

/-- The prime counting function: Returns the number of primes less than or equal to the input.

With `open scoped Nat.Prime`, this has notation `π`. -/
def primeCounting (n : ℕ) : ℕ := primeCounting' (n + 1)

@[inherit_doc] scoped[Nat.Prime] notation "π" => primeCounting

@[inherit_doc] scoped[Nat.Prime] notation "π'" => primeCounting'

open scoped Nat.Prime

theorem primeCounting_eq_primeCounting'_succ (n : ℕ) : π n = π' (n + 1) := rfl

@[simp]
theorem primeCounting_sub_one (n : ℕ) : π (n - 1) = π' n := by cases n <;> rfl

theorem monotone_primeCounting' : Monotone primeCounting' := count_monotone Prime

theorem monotone_primeCounting : Monotone primeCounting :=
  monotone_primeCounting'.comp (monotone_id.add_const _)

@[simp]
theorem primeCounting'_nth_eq (n : ℕ) : π' (nth Prime n) = n :=
  count_nth_of_infinite infinite_setOf_prime _

/-- The `n`th prime is greater or equal to `n + 2`. -/
theorem add_two_le_nth_prime (n : ℕ) : n + 2 ≤ nth Prime n :=
  nth_prime_zero_eq_two ▸ (nth_strictMono infinite_setOf_prime).add_le_nat n 0

theorem surjective_primeCounting' : Function.Surjective π' :=
  surjective_count_of_infinite_setOf infinite_setOf_prime

theorem surjective_primeCounting : Function.Surjective π := by
  suffices Function.Surjective (π ∘ fun n ↦ n - 1) from this.of_comp
  simpa [Function.comp_def] using surjective_primeCounting'

open Filter

theorem tendsto_primeCounting' : Tendsto π' atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone' monotone_primeCounting'
  simp [Set.range_eq_univ.mpr surjective_primeCounting']

theorem tendsto_primeCounting : Tendsto π atTop atTop :=
  (tendsto_add_atTop_iff_nat 1).mpr tendsto_primeCounting'

@[simp]
theorem prime_nth_prime (n : ℕ) : Prime (nth Prime n) :=
  nth_mem_of_infinite infinite_setOf_prime _

@[simp]
lemma primeCounting'_eq_zero_iff {n : ℕ} : n.primeCounting' = 0 ↔ n ≤ 2 := by
  rw [primeCounting', Nat.count_eq_zero ⟨_, prime_two⟩, nth_prime_zero_eq_two]

@[simp]
lemma primeCounting_eq_zero_iff {n : ℕ} : n.primeCounting = 0 ↔ n ≤ 1 := by
  simp [primeCounting, -Order.add_one_le_iff]

@[simp]
lemma primeCounting_zero : primeCounting 0 = 0 := primeCounting_eq_zero_iff.mpr zero_le_one

@[simp]
lemma primeCounting_one : primeCounting 1 = 0 := primeCounting_eq_zero_iff.mpr le_rfl

section PrimeSets

variable {p k n : ℕ}

/-- `primesBelow n` is the set of primes less than `n` as a `Finset`. -/
def primesBelow (n : ℕ) : Finset ℕ := {p ∈ range n | p.Prime}

/-- `primesLE n` is the set of primes less than or equal to `n` as a `Finset`. -/
def primesLE (n : ℕ) : Finset ℕ := primesBelow (n + 1)

lemma primesBelow_eq_filter_range (n : ℕ) : primesBelow n = filter Prime (range n) := rfl

lemma primesLE_eq_filter_range (n : ℕ) : primesLE n = filter Prime (range (n + 1)) := rfl

@[simp]
lemma primesBelow_zero : primesBelow 0 = ∅ := by decide

@[simp]
lemma primesBelow_one : primesBelow 1 = ∅ := by decide

@[simp]
lemma primesBelow_two : primesBelow 2 = ∅ := by decide

@[simp]
lemma primesLE_zero : primesLE 0 = ∅ := primesBelow_one

@[simp]
lemma primesLE_one : primesLE 1 = ∅ := primesBelow_two

theorem primesBelow_eq_primesLE_sub_one (n : ℕ) : primesBelow n = primesLE (n - 1) := by
  cases n <;> simp [primesLE]

lemma mem_primesBelow : n ∈ primesBelow k ↔ n < k ∧ n.Prime := by simp [primesBelow]

lemma mem_primesLE : p ∈ primesLE n ↔ p ≤ n ∧ p.Prime := by simp [primesLE, mem_primesBelow]

lemma prime_of_mem_primesBelow (h : p ∈ n.primesBelow) : p.Prime := (mem_filter.mp h).2

lemma prime_of_mem_primesLE (hp : p ∈ primesLE n) : p.Prime := prime_of_mem_primesBelow hp

lemma lt_of_mem_primesBelow (h : p ∈ n.primesBelow) : p < n := (mem_primesBelow.mp h).1

lemma le_of_mem_primesLE (hp : p ∈ primesLE n) : p ≤ n := (mem_primesLE.mp hp).1

lemma one_lt_of_mem_primesBelow (hp : p ∈ primesBelow n) : 1 < p :=
  (prime_of_mem_primesBelow hp).one_lt

lemma one_lt_of_mem_primesLE (hp : p ∈ primesLE n) : 1 < p := one_lt_of_mem_primesBelow hp

lemma two_le_of_mem_primesBelow (hp : p ∈ primesBelow n) : 2 ≤ p := one_lt_of_mem_primesBelow hp

lemma two_le_of_mem_primesLE (hp : p ∈ primesLE n) : 2 ≤ p := two_le_of_mem_primesBelow hp

lemma primesBelow_eq_filter_Ico_zero (n : ℕ) : primesBelow n = filter Prime (Ico 0 n) := by
  simp [primesBelow_eq_filter_range]

lemma primesLE_eq_filter_Icc_zero (n : ℕ) : primesLE n = filter Prime (Icc 0 n) := by
  ext; simp [primesLE_eq_filter_range]

lemma primesBelow_eq_filter_Ioo_zero (n : ℕ) : primesBelow n = filter Prime (Ioo 0 n) := by
  ext; simp +contextual [primesBelow_eq_filter_range, Prime.pos]

lemma primesLE_eq_filter_Ioc_zero (n : ℕ) : primesLE n = filter Prime (Ioc 0 n) := by
  ext; simp +contextual [primesLE_eq_filter_range, Prime.pos]

lemma primesBelow_eq_filter_Ico_one (n : ℕ) : primesBelow n = filter Prime (Ico 1 n) :=
  primesBelow_eq_filter_Ioo_zero n

lemma primesLE_eq_filter_Icc_one (n : ℕ) : primesLE n = filter Prime (Icc 1 n) :=
  primesLE_eq_filter_Ioc_zero n

lemma primesBelow_eq_filter_Ioo_one (n : ℕ) : primesBelow n = filter Prime (Ioo 1 n) := by
  ext; simp +contextual [primesBelow_eq_filter_range, Prime.one_lt]

lemma primesLE_eq_filter_Ioc_one (n : ℕ) : primesLE n = filter Prime (Ioc 1 n) := by
  ext; simp +contextual [primesLE_eq_filter_range, Prime.one_lt]

lemma primesBelow_eq_filter_Ico_two (n : ℕ) : primesBelow n = filter Prime (Ico 2 n) :=
  primesBelow_eq_filter_Ioo_one n

lemma primesLE_eq_filter_Icc_two (n : ℕ) : primesLE n = filter Prime (Icc 2 n) :=
  primesLE_eq_filter_Ioc_one n

lemma primesBelow_mono : Monotone primesBelow := by intro _ _ _ _; grind [mem_primesBelow]

lemma primesLE_mono : Monotone primesLE := by intro _ _ _ _; grind [mem_primesLE]

lemma primesBelow_succ (n : ℕ) :
    primesBelow (n + 1) = if n.Prime then insert n (primesBelow n) else primesBelow n := by
  rw [primesBelow, primesBelow, range_add_one, filter_insert]

lemma primesLE_succ (n : ℕ) :
    primesLE (n + 1) = if (n + 1).Prime then insert (n + 1) (primesLE n) else primesLE n :=
  primesBelow_succ _

lemma notMem_primesBelow (n : ℕ) : n ∉ primesBelow n :=
  fun hn ↦ (lt_of_mem_primesBelow hn).false

lemma notMem_primesLE (n : ℕ) : n + 1 ∉ primesLE n := notMem_primesBelow _

end PrimeSets

/-- The cardinality of the finset `primesBelow n` equals the counting function
`primeCounting'` at `n`. -/
theorem primesBelow_card_eq_primeCounting' (n : ℕ) : #n.primesBelow = π' n := by
  simpa [primesBelow, primeCounting'] using (count_eq_card_filter_range Prime n).symm

/-- The cardinality of the finset `primesLE n` equals the counting function
`primeCounting` at `n`. -/
@[simp]
theorem primesLE_card_eq_primeCounting (n : ℕ) : #(primesLE n) = π n := by
  simp only [primesLE, primeCounting, primesBelow_card_eq_primeCounting']

/-- A linear upper bound on the size of the `primeCounting'` function -/
theorem primeCounting'_add_le {a k : ℕ} (h0 : a ≠ 0) (h1 : a < k) (n : ℕ) :
    π' (k + n) ≤ π' k + totient a * (n / a + 1) :=
  calc
    π' (k + n) ≤ #{p ∈ range k | p.Prime} + #{p ∈ Ico k (k + n) | p.Prime} := by
      rw [primeCounting', count_eq_card_filter_range, range_eq_Ico, range_eq_Ico, ←
        Ico_union_Ico_eq_Ico (zero_le k) le_self_add, filter_union]
      apply card_union_le
    _ ≤ π' k + #{p ∈ Ico k (k + n) | p.Prime} := by
      rw [primeCounting', count_eq_card_filter_range]
    _ ≤ π' k + #{b ∈ Ico k (k + n) | a.Coprime b} := by
      gcongr with p hp
      rw [coprime_comm]
      exact coprime_of_lt_prime h0 <| h1.trans_le (mem_Ico.1 hp).1
    _ ≤ π' k + totient a * (n / a + 1) := by
      simpa using Ico_filter_coprime_le k n h0

theorem primeCounting_add_le {a k : ℕ} (h0 : a ≠ 0) (h1 : a ≤ k) (n : ℕ) :
    π (k + n) ≤ π k + totient a * (n / a + 1) := by
  rw [primeCounting_eq_primeCounting'_succ, add_right_comm]
  exact primeCounting'_add_le h0 (Order.lt_add_one_iff.mpr h1) n

end Nat
