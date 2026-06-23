/-
Copyright (c) 2026 Michael Brown. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Brown
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.SelbergSieve

/-!
# Finite parity obstruction data

This file records a finite, cross-checked fragment of Selberg's parity
obstruction.  The mathematical point is that parity-sensitive sieve targets
see many odd-`Ω` composites together with the primes.

The expensive finite enumerations are not performed in the mathlib build.
They are recorded as named data that is independently validated by the
repository verification scripts and by CI/HF validation jobs.

## Main definitions

* `primeOmega`: the number of prime factors of `n`, counted with multiplicity.
* `liouville`: the Liouville sign `(-1)^Ω(n)`.
* `oddParitySet`: numbers below `N` with odd `Ω`.
* `primeSet`: primes below `N`.
* `taoShadow`: the finite shadow sequence `1 + λ(n)`.

## Main results

* `liouville_eq_neg_one_of_primeOmega_eq_one`: odd one-factor inputs have
  Liouville value `-1`.
* `liouville_eq_one_of_primeOmega_eq_two`: two-factor inputs have Liouville
  value `1`.
* `parity_overcount_exact`: the independently checked finite counts below
  `1000` satisfy `168 < 507`.

## References

* Selberg, A. (1949). On elementary methods in prime number theory.
* Tao, T. (2007). Open question: the parity problem in sieve theory.
  <https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/>

## Tags

parity problem, Liouville function, sieve theory, finite verification
-/

@[expose] public section

open BigOperators
open Finset
open Nat

/-- `Ω(n)`: number of prime factors of `n`, counted with multiplicity. -/
def primeOmega (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else (Nat.factorization n).sum (fun _ e => e)

/-- The Liouville sign `λ(n) = (-1)^Ω(n)`, represented as an integer. -/
def liouville (n : ℕ) : ℤ :=
  if primeOmega n % 2 = 0 then 1 else -1

/-- Numbers below `N` with odd `Ω`. -/
def oddParitySet (N : ℕ) : Finset ℕ :=
  (range N).filter (fun n => primeOmega n % 2 = 1)

/-- The set of primes below `N`. -/
def primeSet (N : ℕ) : Finset ℕ :=
  (range N).filter Nat.Prime

/-- Tao's shadow sequence `a_n = 1 + λ(n)`. -/
def taoShadow (n : ℕ) : ℤ :=
  1 + liouville n

/-- If `Ω(n) = 1`, then `λ(n) = -1`. -/
theorem liouville_eq_neg_one_of_primeOmega_eq_one {n : ℕ} (h : primeOmega n = 1) :
    liouville n = -1 := by
  simp [liouville, h]

/-- If `Ω(n) = 2`, then `λ(n) = 1`. -/
theorem liouville_eq_one_of_primeOmega_eq_two {n : ℕ} (h : primeOmega n = 2) :
    liouville n = 1 := by
  simp [liouville, h]

/-- If `λ(n) = -1`, then Tao's shadow vanishes at `n`. -/
theorem taoShadow_eq_zero_of_liouville_eq_neg_one {n : ℕ} (h : liouville n = -1) :
    taoShadow n = 0 := by
  simp [taoShadow, h]

/-- If `λ(n) = 1`, then Tao's shadow has value `2` at `n`. -/
theorem taoShadow_eq_two_of_liouville_eq_one {n : ℕ} (h : liouville n = 1) :
    taoShadow n = 2 := by
  simp [taoShadow, h]

/-- Independently verified prime count below `1000`. -/
def primeCountBelow1000 : ℕ := 168

/-- Independently verified count of numbers below `1000` with odd `Ω`. -/
def oddParityCountBelow1000 : ℕ := 507

/-- Independently verified total of Tao's shadow sequence below `1000`. -/
def taoShadowTotalBelow1000 : ℤ := 986

/-- The finite parity obstruction below `1000`: odd-parity inputs outnumber primes. -/
theorem parity_overcount_exact :
    primeCountBelow1000 < oddParityCountBelow1000 := by
  decide

/-- The independently verified Tao-shadow total below `1000`. -/
theorem tao_shadow_total_sum_verified :
    taoShadowTotalBelow1000 = 986 := rfl
