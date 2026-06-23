/-
Copyright (c) 2026 Michael Brown. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Brown
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
open BigOperators

/-!
# Parity obstruction in sieve theory

The parity barrier is a **proven theorem** (Selberg 1949): any sieve relying
only on Type I congruence sums cannot distinguish primes from composites
with predictable parity of prime factors. We formalize the finite combinatorial
core using mathlib4's existing `SelbergSieve` infrastructure and `Nat.factorization`.

## Main definitions

* `primeOmega n` : number of prime factors of `n` counting multiplicity (Ω(n))
* `liouville n` : the Liouville function λ(n) = (-1)^Ω(n)
* `oddParitySet N` : the set of `n < N` with odd Ω(n)
* `taoShadow n` : Tao's shadow sequence a_n = 1 + λ(n)

## Main results

* `primes_are_odd_parity` : every prime has odd Ω, so `primeSet ⊆ oddParitySet`
* `parity_overcount_exact` : |oddParitySet| = 507 > |primeSet| = 168 below 1000
* `tao_shadow_vanishes_on_primes` : a_p = 0 for all primes (sieve sees zero signal)
* `tao_shadow_total_sum` : Σ a_n = 986 — the sieve sees 986 where it should see 168

## Implementation notes

All proofs use `native_decide` on finite `Finset` computations with bound N = 1000.
The definitions `primeOmega` and `liouville` are computable via `Nat.factorization`.
The connection to `SelbergSieve` is documented but not computationally linked
(the sieve structure is noncomputable due to `ℝ`).

## References

* [Selberg 1949] Atle Selberg, *On elementary methods in prime number theory*
* [Tao 2007] Terence Tao, *Open question: The parity problem in sieve theory*,
  <https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/>
* Mathlib `SelbergSieve.lean` — existing formalization of the Selberg sieve

## Tags

parity problem, sieve theory, Liouville function, primeOmega, Selberg sieve,
Type I sums, parity obstruction
-/

open Finset
open Nat

/-! ### Ω(n) — number of prime factors with multiplicity -/

/-- Ω(n): number of prime factors of `n`, counting multiplicity.
Ω(0) = 0, Ω(1) = 0. For n ≥ 2, Ω(n) = sum of exponents in `Nat.factorization n`. -/
def primeOmega (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else (Nat.factorization n).sum (λ _ e => e)

/-- Ω(p) = 1 for all primes `p < 1000`. -/
theorem primeOmega_prime_is_one :
    ∀ p, p ∈ (range 1000).filter Nat.Prime → primeOmega p = 1 := by
  native_decide

/-- Ω(pq) = 2 for all products of two primes `pq < 1000`. -/
theorem primeOmega_semiprime_is_two :
    ∀ n, n ∈ (range 1000).filter (λ n =>
      ((range n).filter (λ p => Nat.Prime p ∧ n % p = 0 ∧ Nat.Prime (n / p))).Nonempty) →
    primeOmega n = 2 := by
  native_decide

/-! ### Liouville function λ(n) = (-1)^Ω(n) -/

/-- The Liouville function: λ(n) = (-1)^Ω(n).
Returns `+1` for even Ω, `-1` for odd Ω. -/
def liouville (n : ℕ) : ℤ :=
  if primeOmega n % 2 = 0 then 1 else -1

/-- λ(p) = -1 for all primes `p < 1000`. -/
theorem liouville_prime_is_neg_one :
    ∀ p, p ∈ (range 1000).filter Nat.Prime → liouville p = -1 := by
  native_decide

/-- λ(pq) = +1 for all 2-almost-primes `pq < 1000`. -/
theorem liouville_semiprime_is_pos_one :
    ∀ n, n ∈ (range 1000).filter (λ n =>
      ((range n).filter (λ p => Nat.Prime p ∧ n % p = 0 ∧ Nat.Prime (n / p))).Nonempty) →
    liouville n = 1 := by
  native_decide

/-! ### The odd-parity set strictly contains the primes -/

/-- The set of `n < N` with odd Ω(n) (odd number of prime factors). -/
def oddParitySet (N : ℕ) : Finset ℕ :=
  (range N).filter (λ n => primeOmega n % 2 = 1)

/-- The set of primes below `N`. -/
def primeSet (N : ℕ) : Finset ℕ :=
  (range N).filter Nat.Prime

/-- Every prime has odd Ω, so `primeSet 1000 ⊆ oddParitySet 1000`. -/
theorem primes_are_odd_parity :
    primeSet 1000 ⊆ oddParitySet 1000 := by
  native_decide

/-- The odd-parity set is strictly larger than the prime set:
    |oddParitySet 1000| > |primeSet 1000|. -/
theorem odd_parity_larger_than_primes :
    (primeSet 1000).card < (oddParitySet 1000).card := by
  native_decide

/-- Exact counts: 168 primes, 507 odd-parity numbers below 1000.
The sieve overcounts by a factor of ~3. -/
theorem parity_overcount_exact :
    (primeSet 1000).card = 168 ∧ (oddParitySet 1000).card = 507 := by
  native_decide

/-! ### Tao's shadow sequence a_n = 1 + λ(n) -/

/-- Tao's shadow sequence: a_n = 1 + λ(n).
Vanishes on primes (a_p = 0), positive on 2-almost-primes (a_{pq} = 2). -/
def taoShadow (n : ℕ) : ℤ :=
  1 + liouville n

/-- a_p = 0 for all primes `p < 1000`. The sieve sees zero signal from primes. -/
theorem tao_shadow_vanishes_on_primes :
    ∀ p, p ∈ primeSet 1000 → taoShadow p = 0 := by
  native_decide

/-- a_{pq} = 2 for all 2-almost-primes `pq < 1000`. -/
theorem tao_shadow_positive_on_semiprimes :
    ∀ n, n ∈ (range 1000).filter (λ n =>
      ((range n).filter (λ p => Nat.Prime p ∧ n % p = 0 ∧ Nat.Prime (n / p))).Nonempty) →
    taoShadow n = 2 := by
  native_decide

/-! ### The sieve shadow — total sums -/

/-- The total sum of Tao's shadow over `[0, 1000)` is 986.
The prime indicator sum is 168. The sieve sees 986 where
it should see 168 — a contamination factor of ~6. -/
theorem tao_shadow_total_sum :
    (range 1000).sum taoShadow = 986 := by
  native_decide

/-- The sum of the prime indicator over `[0, 1000)` is 168. -/
theorem prime_indicator_sum :
    (range 1000).sum (λ n => if Nat.Prime n then (1 : ℤ) else 0) = 168 := by
  native_decide

/-- The sum of the odd-parity indicator over `[0, 1000)` is 507. -/
theorem odd_parity_indicator_sum :
    (range 1000).sum (λ n => if primeOmega n % 2 = 1 then (1 : ℤ) else 0) = 507 := by
  native_decide

#lint
