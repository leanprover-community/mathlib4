/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.prime_fin
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Factors
import Mathbin.Data.Set.Finite

/-!
# Prime numbers

This file contains some results about prime numbers which depend on finiteness of sets.
-/


namespace Nat

/-- A version of `nat.exists_infinite_primes` using the `set.infinite` predicate. -/
theorem infinite_setOf_prime : { p | Prime p }.Infinite :=
  Set.infinite_of_not_bddAbove not_bddAbove_setOf_prime
#align nat.infinite_set_of_prime Nat.infinite_setOf_prime

/-- If `a`, `b` are positive, the prime divisors of `a * b` are the union of those of `a` and `b` -/
theorem factors_mul_toFinset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factors.toFinset = a.factors.toFinset ∪ b.factors.toFinset :=
  (List.toFinset.ext fun x => (mem_factors_mul ha hb).trans List.mem_union.symm).trans <|
    List.toFinset_union _ _
#align nat.factors_mul_to_finset Nat.factors_mul_toFinset

theorem pow_succ_factors_toFinset (n k : ℕ) : (n ^ (k + 1)).factors.toFinset = n.factors.toFinset :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  induction' k with k ih
  · simp
  rw [pow_succ, factors_mul_to_finset hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]
#align nat.pow_succ_factors_to_finset Nat.pow_succ_factors_toFinset

theorem pow_factors_toFinset (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (n ^ k).factors.toFinset = n.factors.toFinset :=
  by
  cases k
  · simpa using hk
  rw [pow_succ_factors_to_finset]
#align nat.pow_factors_to_finset Nat.pow_factors_toFinset

/-- The only prime divisor of positive prime power `p^k` is `p` itself -/
theorem prime_pow_prime_divisor {p k : ℕ} (hk : k ≠ 0) (hp : Prime p) :
    (p ^ k).factors.toFinset = {p} := by simp [pow_factors_to_finset p hk, factors_prime hp]
#align nat.prime_pow_prime_divisor Nat.prime_pow_prime_divisor

theorem factors_mul_toFinset_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).factors.toFinset = a.factors.toFinset ∪ b.factors.toFinset :=
  (List.toFinset.ext <| mem_factors_mul_of_coprime hab).trans <| List.toFinset_union _ _
#align nat.factors_mul_to_finset_of_coprime Nat.factors_mul_toFinset_of_coprime

end Nat

