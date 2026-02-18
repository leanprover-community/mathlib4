/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import Mathlib.Algebra.Ring.Identities
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

/-!
# IMO 1969 Q1

Prove that there are infinitely many natural numbers $a$ with the following property:
the number $z = n^4 + a$ is not prime for any natural number $n$.
-/


open Int Nat

namespace Imo1969Q1

/-- `goodNats` is the set of natural numbers satisfying the condition in the problem
statement, namely the `a : ℕ` such that `n^4 + a` is not prime for any `n : ℕ`. -/
def goodNats : Set ℕ :=
  {a : ℕ | ∀ n : ℕ, ¬Nat.Prime (n ^ 4 + a)}

/-!
The key to the solution is that you can factor $z$ into the product of two polynomials,
if $a = 4*m^4$. This is Sophie Germain's identity, called `pow_four_add_four_mul_pow_four`
in mathlib.
-/


theorem factorization {m n : ℤ} :
    ((n - m) ^ 2 + m ^ 2) * ((n + m) ^ 2 + m ^ 2) = n ^ 4 + 4 * m ^ 4 :=
  pow_four_add_four_mul_pow_four.symm

/-!
To show that the product is not prime, we need to show each of the factors is at least 2,
which `nlinarith` can solve since they are each expressed as a sum of squares.
-/


theorem left_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < (n - m) ^ 2 + m ^ 2 := by nlinarith

theorem right_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < (n + m) ^ 2 + m ^ 2 := by nlinarith

/-!
The factorization is over the integers, but we need the nonprimality over the natural numbers.
-/


theorem int_large {m : ℤ} (h : 1 < m) : 1 < m.natAbs := by
  exact_mod_cast lt_of_lt_of_le h le_natAbs

theorem not_prime_of_int_mul' {m n : ℤ} {c : ℕ} (hm : 1 < m) (hn : 1 < n) (hc : m * n = (c : ℤ)) :
    ¬Nat.Prime c :=
  not_prime_of_int_mul (int_large hm).ne' (int_large hn).ne' hc

/-- Every natural number of the form `n^4 + 4*m^4` is not prime. -/
theorem polynomial_not_prime {m : ℕ} (h1 : 1 < m) (n : ℕ) : ¬Nat.Prime (n ^ 4 + 4 * m ^ 4) := by
  have h2 : 1 < (m : ℤ) := Int.ofNat_lt.mpr h1
  refine not_prime_of_int_mul' (left_factor_large (n : ℤ) h2) (right_factor_large (n : ℤ) h2) ?_
  apply factorization

/-- We define $a_{choice}(b) := 4*(2+b)^4$, so that we can take $m = 2+b$ in `polynomial_not_prime`.
-/
def aChoice (b : ℕ) : ℕ :=
  4 * (2 + b) ^ 4

theorem aChoice_good (b : ℕ) : aChoice b ∈ goodNats :=
  polynomial_not_prime (show 1 < 2 + b by linarith)

/-- `aChoice` is a strictly monotone function; this is easily proven by chaining together lemmas
in the `strictMono` namespace. -/
theorem aChoice_strictMono : StrictMono aChoice :=
  ((strictMono_id.const_add 2).nat_pow (by decide)).const_mul (by decide)

end Imo1969Q1

open Imo1969Q1

/-- We conclude by using the fact that `aChoice` is an injective function from the natural numbers
to the set `goodNats`. -/
theorem imo1969_q1 : Set.Infinite {a : ℕ | ∀ n : ℕ, ¬Nat.Prime (n ^ 4 + a)} :=
  Set.infinite_of_injective_forall_mem aChoice_strictMono.injective aChoice_good
