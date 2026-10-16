/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Almost prime numbers

This file defines `Nat.IsAlmostPrime k n`, the predicate that `n` has exactly `k`
prime factors counted with multiplicity. We also define `Nat.IsAtMostAlmostPrime`,
the corresponding predicate with at most `k` prime factors, and `Nat.IsSemiprime`,
the special case of `2`-almost-prime numbers.

Both definitions use the arithmetic function `ArithmeticFunction.cardFactors`, written `Ω`.

The terminology follows the standard definition of an
[almost prime](https://en.wikipedia.org/wiki/Almost_prime).

## Main statements

* `Nat.IsAlmostPrime.mul`: the product of a `k`-almost-prime number and an
  `l`-almost-prime number is `(k + l)`-almost-prime.
* `Nat.IsAtMostAlmostPrime.mul`: the analogous statement for at most `k` prime factors.

-/

@[expose] public section

open scoped ArithmeticFunction.Omega

namespace Nat

/-- `IsAlmostPrime k n` means that `n` is `k`-almost prime: it has exactly `k`
prime factors, counted with multiplicity. The side condition excludes `0`, so `1` is
`0`-almost prime. -/
def IsAlmostPrime (k n : ℕ) : Prop :=
  n ≠ 0 ∧ Ω n = k

/-- `IsAtMostAlmostPrime k n` means that `n` has at most `k` prime factors,
counted with multiplicity. -/
def IsAtMostAlmostPrime (k n : ℕ) : Prop :=
  n ≠ 0 ∧ Ω n ≤ k

/-- A semiprime is a `2`-almost-prime number. -/
abbrev IsSemiprime (n : ℕ) : Prop :=
  IsAlmostPrime 2 n

variable {k l m n p q : ℕ}

@[simp]
theorem isAlmostPrime_zero_iff : IsAlmostPrime 0 n ↔ n = 1 := by
  rw [IsAlmostPrime, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]
  exact ⟨fun h ↦ h.2.resolve_left h.1, fun h ↦ by simp [h]⟩

@[simp]
theorem isAlmostPrime_one_iff : IsAlmostPrime 1 n ↔ n.Prime := by
  constructor
  · exact fun h ↦ ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h.2
  · exact fun h ↦ ⟨h.ne_zero, ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr h⟩

theorem Prime.isAlmostPrime_one (hp : p.Prime) : IsAlmostPrime 1 p := by
  simpa using isAlmostPrime_one_iff.mpr hp

theorem IsAlmostPrime.mul (hm : IsAlmostPrime k m) (hn : IsAlmostPrime l n) :
    IsAlmostPrime (k + l) (m * n) := by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1, hm.2, hn.2]

theorem IsAtMostAlmostPrime.mul (hm : IsAtMostAlmostPrime k m) (hn : IsAtMostAlmostPrime l n) :
    IsAtMostAlmostPrime (k + l) (m * n) := by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1]
  exact add_le_add hm.2 hn.2

theorem IsAlmostPrime.isAtMost (hn : IsAlmostPrime k n) (hkl : k ≤ l) :
    IsAtMostAlmostPrime l n :=
  ⟨hn.1, hn.2 ▸ hkl⟩

theorem Prime.mul_isAlmostPrime_two (hp : p.Prime) (hq : q.Prime) :
    IsAlmostPrime 2 (p * q) := by
  simpa using hp.isAlmostPrime_one.mul hq.isAlmostPrime_one

theorem Prime.sq_isAlmostPrime_two (hp : p.Prime) : IsAlmostPrime 2 (p ^ 2) := by
  simpa [pow_two] using hp.mul_isAlmostPrime_two hp

end Nat
