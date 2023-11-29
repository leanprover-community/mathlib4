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

open Pointwise Finset

namespace Nat

lemma divisors_mul {m n : ℕ} : divisors (m * n) = divisors m * divisors n := by
  ext k
  simp_rw [mem_mul, mem_divisors, dvd_mul, mul_ne_zero_iff, ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

lemma Prime.divisors_sq {p : ℕ} (hp : p.Prime) : (p ^ 2).divisors = {p ^ 2, p, 1} := by
  simp [divisors_prime_pow hp, range_succ]

end Nat

open Nat

lemma List.nat_divisors_prod (l : List ℕ) : divisors l.prod = (l.map divisors).prod := by
  induction l with
  | nil => simp; rfl
  | cons head tail hl => simp [divisors_mul, hl]

lemma Multiset.divisors_prod (s : Multiset ℕ) : divisors s.prod = (s.map divisors).prod := by
  apply s.induction (by simp; rfl) fun  a s hs ↦ by simp [hs, divisors_mul]
