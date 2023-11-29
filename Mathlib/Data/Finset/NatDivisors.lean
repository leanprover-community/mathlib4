/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Divisors

/-!
#  Divisors of a product

The divisors of a product of natural numbers are the pointwise product of the divisors of the
factors.
-/

namespace Nat

open Pointwise Finset

lemma Prime.divisors_mul (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (p * n).divisors = p.divisors * n.divisors := by
  ext
  simp only [mem_mul, Nat.mem_divisors, Nat.isUnit_iff, Nat.dvd_mul, Nat.dvd_prime hp,
    exists_and_left, exists_eq_or_imp, one_mul, exists_eq_right', exists_eq_left, ne_eq,
    mul_eq_zero, hp.divisors, mem_singleton, mem_insert, exists_eq_right]
  aesop

lemma divisors_mul {m n : ℕ} : divisors (m * n) = divisors m * divisors n := by
  apply induction_on_primes (by simp) ?_ (fun p a hp han => ?_) m
  · rw [divisors_one, one_mul]
    exact (one_mul (M := Finset ℕ) _).symm
  · simp only [mul_assoc, hp.divisors_mul, han]

lemma Prime.divisors_sq {p : ℕ} (hp : p.Prime) : (p ^ 2).divisors = {1, p, p ^ 2} := by
  ext
  simp only [sq, Nat.divisors_mul, hp.divisors, mem_singleton, mem_mul, mem_insert, exists_and_left,
    exists_eq_or_imp, mul_one, exists_eq_left, one_mul, ne_eq]
  aesop
