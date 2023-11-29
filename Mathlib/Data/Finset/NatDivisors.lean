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

lemma divisors_mul {m n : ℕ} : divisors (m * n) = divisors m * divisors n := by
  ext k
  simp_rw [mem_mul, mem_divisors, dvd_mul, mul_ne_zero_iff, ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

lemma Prime.divisors_sq {p : ℕ} (hp : p.Prime) : (p ^ 2).divisors = {1, p, p ^ 2} := by
  ext
  simp only [sq, Nat.divisors_mul, hp.divisors, mem_singleton, mem_mul, mem_insert, exists_and_left,
    exists_eq_or_imp, mul_one, exists_eq_left, one_mul, ne_eq]
  aesop
