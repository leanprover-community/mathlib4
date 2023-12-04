/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Prime

#align_import algebra.char_p.exp_char from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Exponential characteristic

This file defines the exponential characteristic, which is defined to be 1 for a ring with
characteristic 0 and the same as the ordinary characteristic, if the ordinary characteristic is
prime. This concept is useful to simplify some theorem statements.
This file establishes a few basic results relating it to the (ordinary characteristic).
The definition is stated for a semiring, but the actual results are for nontrivial rings
(as far as exponential characteristic one is concerned), respectively a ring without zero-divisors
(for prime characteristic).

## Main results
- `ExpChar`: the definition of exponential characteristic
- `expChar_is_prime_or_one`: the exponential characteristic is a prime or one
- `char_eq_expChar_iff`: the characteristic equals the exponential characteristic iff the
  characteristic is prime

## Tags
exponential characteristic, characteristic
-/


universe u

variable (R : Type u)

section Semiring

variable [Semiring R]

/-- The definition of the exponential characteristic of a semiring. -/
class inductive ExpChar (R : Type u) [Semiring R] : ℕ → Prop
  | zero [CharZero R] : ExpChar R 1
  | prime {q : ℕ} (hprime : q.Prime) [hchar : CharP R q] : ExpChar R q
#align exp_char ExpChar
#align exp_char.prime ExpChar.prime

/-- The exponential characteristic is one if the characteristic is zero. -/
theorem expChar_one_of_char_zero (q : ℕ) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by
  cases' hq with q hq_one hq_prime hq_hchar
  · rfl
  · exact False.elim (lt_irrefl _ ((hp.eq R hq_hchar).symm ▸ hq_prime : (0 : ℕ).Prime).pos)
#align exp_char_one_of_char_zero expChar_one_of_char_zero

/-- The characteristic equals the exponential characteristic iff the former is prime. -/
theorem char_eq_expChar_iff (p q : ℕ) [hp : CharP R p] [hq : ExpChar R q] : p = q ↔ p.Prime := by
  cases' hq with q hq_one hq_prime hq_hchar
  · rw [(CharP.eq R hp inferInstance : p = 0)]
    decide
  · exact ⟨fun hpq => hpq.symm ▸ hq_prime, fun _ => CharP.eq R hp hq_hchar⟩
#align char_eq_exp_char_iff char_eq_expChar_iff

section Nontrivial

variable [Nontrivial R]

/-- The exponential characteristic is one if the characteristic is zero. -/
theorem char_zero_of_expChar_one (p : ℕ) [hp : CharP R p] [hq : ExpChar R 1] : p = 0 := by
  cases hq
  · exact CharP.eq R hp inferInstance
  · exact False.elim (CharP.char_ne_one R 1 rfl)
#align char_zero_of_exp_char_one char_zero_of_expChar_one

-- This could be an instance, but there are no `ExpChar R 1` instances in mathlib.
/-- The characteristic is zero if the exponential characteristic is one. -/
theorem charZero_of_expChar_one' [hq : ExpChar R 1] : CharZero R := by
  cases hq
  · assumption
  · exact False.elim (CharP.char_ne_one R 1 rfl)
#align char_zero_of_exp_char_one' charZero_of_expChar_one'

/-- The exponential characteristic is one iff the characteristic is zero. -/
theorem expChar_one_iff_char_zero (p q : ℕ) [CharP R p] [ExpChar R q] : q = 1 ↔ p = 0 := by
  constructor
  · rintro rfl
    exact char_zero_of_expChar_one R p
  · rintro rfl
    exact expChar_one_of_char_zero R q
#align exp_char_one_iff_char_zero expChar_one_iff_char_zero

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- A helper lemma: the characteristic is prime if it is non-zero. -/
theorem char_prime_of_ne_zero {p : ℕ} [hp : CharP R p] (p_ne_zero : p ≠ 0) : Nat.Prime p := by
  cases' CharP.char_is_prime_or_zero R p with h h
  · exact h
  · contradiction
#align char_prime_of_ne_zero char_prime_of_ne_zero

/-- The exponential characteristic is a prime number or one. -/
theorem expChar_is_prime_or_one (q : ℕ) [hq : ExpChar R q] : Nat.Prime q ∨ q = 1 := by
  cases hq
  case zero => exact .inr rfl
  case prime hp _ => exact .inl hp
#align exp_char_is_prime_or_one expChar_is_prime_or_one

end NoZeroDivisors

end Nontrivial

end Semiring
