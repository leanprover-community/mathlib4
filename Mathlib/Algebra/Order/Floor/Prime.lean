/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Existence of a sufficiently large prime for which `a * c ^ p / (p - 1)! < 1`

This is a technical result used in the proof of the Lindemann-Weierstrass theorem.

TODO: delete this file, as all its lemmas have been deprecated.
-/

open scoped Nat

@[deprecated eventually_mul_pow_lt_factorial_sub (since := "2024-09-25")]
theorem Nat.exists_prime_mul_pow_lt_factorial (n a c : ℕ) :
    ∃ p > n, p.Prime ∧ a * c ^ p < (p - 1)! :=
  ((Filter.frequently_atTop.mpr Nat.exists_infinite_primes).and_eventually
    (eventually_mul_pow_lt_factorial_sub a c 1)).forall_exists_of_atTop (n + 1)

namespace FloorRing

variable {K : Type*}

@[deprecated FloorSemiring.eventually_mul_pow_lt_factorial_sub (since := "2024-09-25")]
theorem exists_prime_mul_pow_lt_factorial [LinearOrderedRing K] [FloorRing K] (n : ℕ) (a c : K) :
    ∃ p > n, p.Prime ∧ a * c ^ p < (p - 1)! :=
  ((Filter.frequently_atTop.mpr Nat.exists_infinite_primes).and_eventually
    (FloorSemiring.eventually_mul_pow_lt_factorial_sub a c 1)).forall_exists_of_atTop (n + 1)

@[deprecated FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (since := "2024-09-25")]
theorem exists_prime_mul_pow_div_factorial_lt_one [LinearOrderedField K] [FloorRing K]
    (n : ℕ) (a c : K) :
    ∃ p > n, p.Prime ∧ a * c ^ p / (p - 1)! < 1 :=
  letI := Preorder.topology K
  haveI : OrderTopology K := ⟨rfl⟩
  ((Filter.frequently_atTop.mpr Nat.exists_infinite_primes).and_eventually
    (Filter.Tendsto.eventually_lt_const zero_lt_one
      (FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop a c 1))).forall_exists_of_atTop
    (n + 1)

end FloorRing
